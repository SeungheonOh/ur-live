{-# LANGUAGE DerivingStrategies #-}

-- | Shared state for monomorphic type lowering.  Core has already specialized
-- parameterized datatypes; the zero-parameter instance table preserves those
-- datatype and constructor identities while recursive payloads are lowered.
module Vr.Mono.Lower.State
  ( MonoM
  , MonoState (..)
  , DatatypeDef (..)
  , DatatypeInstance (..)
  , initialMonoState
  , runMonoM
  , monoType
  , monoStaticArg
  , monoName
  , monoPatCon
  , unitType
  , getUrlPrefix
  , mayClientToServer
  , lookupRpcTarget
  , monoFunctionDomains
  , reserveUrlifyHelper
  , emitGeneratedValue
  , urlDatatypeConstructors
  ) where

import Control.Monad.State.Strict (StateT (..), get, modify', runStateT)
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Vr.Core.Substitute as Substitute
import qualified Vr.Core.Syntax as C
import Vr.Middle (Effect, ExportKind (Rpc))
import qualified Vr.Mono.Syntax as M
import Vr.Source (Diagnostic, DiagnosticPhase (MonoPhase), Located (..), Span, diagnostic, noSpan)

data DatatypeDef = DatatypeDef
  { datatypeName :: !String
  , datatypeParameters :: ![String]
  , datatypeConstructors :: ![(String, C.GlobalId, Maybe C.Con)]
  , datatypeClassification :: !C.DatatypeKind
  }
  deriving stock (Eq, Ord, Show)

data DatatypeInstance = DatatypeInstance
  { instanceTypeId :: !M.GlobalId
  , instanceConstructors :: !(Map.Map C.GlobalId M.GlobalId)
  }
  deriving stock (Eq, Ord, Show)

data MonoState = MonoState
  { monoNextId :: !Int
  , monoAliases :: !(Map.Map C.GlobalId C.Con)
  , monoDatatypes :: !(Map.Map C.GlobalId DatatypeDef)
  , monoConstructorParents :: !(Map.Map C.GlobalId C.GlobalId)
  , monoInstances :: !(Map.Map (C.GlobalId, [C.Con]) DatatypeInstance)
  , monoGeneratedDatatypes :: ![M.Decl]
  , monoGeneratedValues :: ![M.Decl]
  , monoUrlifyHelpers :: !(Map.Map M.Type M.GlobalId)
  , monoUrlPrefix :: !String
  , monoClientToServer :: !(Set (String, String))
  , monoValueInfo :: !(Map.Map C.GlobalId (C.Con, String))
  , monoRpcEffects :: !(Map.Map C.GlobalId Effect)
  }

type MonoM = StateT MonoState (Either Diagnostic)

initialMonoState :: Int -> C.File -> MonoState
initialMonoState next file =
  MonoState
    { monoNextId = next
    , monoAliases = Map.fromList
        [ (identifier, definition)
        | declaration <- file
        , C.DCon _ identifier _ definition <- [locatedValue declaration]
        ]
    , monoDatatypes = datatypeMap
    , monoConstructorParents = Map.fromList
        [ (constructorId, datatypeId)
        | (datatypeId, definition) <- Map.toList datatypeMap
        , (_, constructorId, _) <- datatypeConstructors definition
        ]
    , monoInstances = Map.fromList
        [ ( (identifier, [])
          , DatatypeInstance identifier (Map.fromList [(constructor, constructor) | (_, constructor, _) <- datatypeConstructors definition])
          )
        | (identifier, definition) <- Map.toList datatypeMap
        , null (datatypeParameters definition)
        ]
    , monoGeneratedDatatypes = []
    , monoGeneratedValues = []
    , monoUrlifyHelpers = Map.empty
    , monoUrlPrefix = "/"
    , monoClientToServer = Set.empty
    , monoValueInfo = Map.fromList
        [ (identifier, (typ, url))
        | declaration <- file
        , binding <- case locatedValue declaration of
            C.DVal _ identifier typ _ url -> [(identifier, typ, url)]
            C.DValRec values -> [(identifier, typ, url) | (_, identifier, typ, _, url) <- values]
            _ -> []
        , let (identifier, typ, url) = binding
        ]
    , monoRpcEffects = Map.fromList
        [ (identifier, effect)
        | declaration <- file
        , C.DExport (Rpc effect) identifier _ <- [locatedValue declaration]
        ]
    }
  where
    datatypeMap = Map.fromList
      [ (identifier, DatatypeDef name parameters constructors (classify constructors))
      | declaration <- file
      , C.DDatatype definitions <- [locatedValue declaration]
      , (name, identifier, parameters, constructors) <- definitions
      ]

mayClientToServer :: String -> String -> MonoM Bool
mayClientToServer moduleName typeName = do
  state <- get
  pure (Set.member (moduleName, typeName) (monoClientToServer state))

runMonoM :: MonoState -> MonoM value -> Either Diagnostic (value, MonoState)
runMonoM state action = runStateT action state

getUrlPrefix :: MonoM String
getUrlPrefix = monoUrlPrefix <$> get

lookupRpcTarget :: C.GlobalId -> MonoM (Maybe (C.Con, String, Effect))
lookupRpcTarget identifier = do
  state <- get
  pure $ do
    (typ, url) <- Map.lookup identifier (monoValueInfo state)
    effect <- Map.lookup identifier (monoRpcEffects state)
    pure (typ, url, effect)

monoFunctionDomains :: Int -> C.Con -> MonoM [M.Type]
monoFunctionDomains count = go count []
  where
    go remaining domains source
      | remaining == 0 = pure (reverse domains)
      | otherwise = do
          expanded <- expandAliases Set.empty (Substitute.normalizeCon source)
          case locatedValue expanded of
            C.TFun domain range -> do
              domain' <- monoType domain
              go (remaining - 1) (domain' : domains) range
            _ -> monoFailureAt "rpc-arguments" "RPC target type has fewer arguments than its call"

-- Reserve the identity before constructing a helper body, so recursive and
-- mutually recursive URL serializers can refer back to helpers already being
-- built.  Source locations are erased from the memo key just as they are for
-- Core specialization identities.
reserveUrlifyHelper :: M.Type -> MonoM (M.GlobalId, Bool)
reserveUrlifyHelper typ = do
  state <- get
  let key = canonicalMonoType typ
  case Map.lookup key (monoUrlifyHelpers state) of
    Just identifier -> pure (identifier, False)
    Nothing -> do
      let identifier = M.GlobalId (monoNextId state)
      modify' $ \current -> current
        { monoNextId = monoNextId current + 1
        , monoUrlifyHelpers = Map.insert key identifier (monoUrlifyHelpers current)
        }
      pure (identifier, True)

emitGeneratedValue :: M.Decl -> MonoM ()
emitGeneratedValue declaration =
  modify' $ \state -> state {monoGeneratedValues = declaration : monoGeneratedValues state}

-- Recover the constructors belonging to a concrete Mono datatype instance.
-- Specialized instances retain their Core arguments in monoInstances, which
-- lets us instantiate payload types without duplicating datatype logic in the
-- main lowering module.
urlDatatypeConstructors
  :: M.GlobalId
  -> MonoM (C.DatatypeKind, [(String, M.GlobalId, Maybe M.Type)])
urlDatatypeConstructors identifier = do
  state <- get
  case
    [ (arguments, definition, instance')
    | ((sourceId, arguments), instance') <- Map.toList (monoInstances state)
    , instanceTypeId instance' == identifier
    , Just definition <- [Map.lookup sourceId (monoDatatypes state)]
    ] of
    (arguments, definition, instance') : _ -> do
      constructors <- mapM (instantiateConstructor arguments instance') (datatypeConstructors definition)
      pure (datatypeClassification definition, constructors)
    [] -> monoFailureAt "urlify-datatype" "URL serializer refers to an unknown datatype instance"

canonicalMonoType :: M.Type -> M.Type
canonicalMonoType typ = Located noSpan $ case locatedValue typ of
  M.TFun domain range -> M.TFun (canonicalMonoType domain) (canonicalMonoType range)
  M.TRecord fields -> M.TRecord [(name, canonicalMonoType fieldType) | (name, fieldType) <- fields]
  M.TOption element -> M.TOption (canonicalMonoType element)
  M.TList element -> M.TList (canonicalMonoType element)
  M.TSignal element -> M.TSignal (canonicalMonoType element)
  other -> other

monoType :: C.Con -> MonoM M.Type
monoType source0 = do
  source <- expandAliases Set.empty (Substitute.normalizeCon source0)
  let at = locatedSpan source
      located = Located at
  case locatedValue source of
    C.TFun domain range -> located <$> (M.TFun <$> monoType domain <*> monoType range)
    C.TRecord row -> case locatedValue (Substitute.normalizeCon row) of
      C.CRecord _ fields -> do
        names <- mapM (monoNameMaybe . fst) fields
        case sequence names of
          Just concrete -> do
            types <- mapM (monoType . snd) fields
            pure (located (M.TRecord (sortOn fst (zip concrete types))))
          Nothing -> monoFailure source "mono-row" "Runtime record type retained a non-concrete field name"
      _ -> monoFailure source "mono-row" "Runtime record type retained a non-concrete row"
    C.CNamed identifier -> monoDatatypeType source identifier []
    C.CFfi moduleName name -> pure (plainFfiType at moduleName name)
    C.CApp {} -> do
      let (headConstructor, arguments) = collectApplications source
      head' <- expandAliases Set.empty headConstructor
      case locatedValue head' of
        C.CNamed identifier -> monoDatatypeType source identifier arguments
        C.CFfi moduleName name -> appliedFfiType at moduleName name arguments
        _ -> monoFailure source "mono-type" "Applied constructor is not a concrete runtime type"
    C.CUnit -> pure (unitType at)
    C.TCFun {} -> monoFailure source "polymorphic-type" "Constructor-polymorphic type survived Core specialization"
    C.TKFun {} -> monoFailure source "polymorphic-type" "Kind-polymorphic type survived Core specialization"
    C.CRel {} -> monoFailure source "open-type" "Open constructor survived Core specialization"
    _ -> monoFailure source "mono-type" "Constructor is not a concrete runtime type"

monoNameMaybe :: C.Con -> MonoM (Maybe String)
monoNameMaybe source = do
  normalized <- expandAliases Set.empty (Substitute.normalizeCon source)
  pure $ case locatedValue normalized of
    C.CName name -> Just name
    _ -> Nothing

plainFfiType :: Span -> String -> String -> M.Type
plainFfiType at moduleName name
  | moduleName == "Basis" && name == "unit" = unitType at
  | moduleName == "Basis" && name `elem` stringLikeTypes = Located at (M.TFfi "Basis" "string")
  | otherwise = Located at (M.TFfi moduleName name)

appliedFfiType :: Span -> String -> String -> [C.Con] -> MonoM M.Type
appliedFfiType at "Basis" name arguments = case (name, arguments) of
  ("option", [element]) -> Located at . M.TOption <$> monoType element
  ("list", [element]) -> Located at . M.TList <$> monoType element
  ("transaction", [result]) -> Located at . M.TFun (unitType at) <$> monoType result
  ("source", [_]) -> pure (Located at M.TSource)
  ("signal", [element]) -> Located at . M.TSignal <$> monoType element
  ("eq", [element]) -> do
    typ <- monoType element
    pure (function2 at typ typ (Located at (M.TFfi "Basis" "bool")))
  ("show", [element]) -> do
    typ <- monoType element
    pure (Located at (M.TFun typ (Located at (M.TFfi "Basis" "string"))))
  ("read", [element]) -> readDictionary at <$> monoType element
  ("num", [element]) -> numericDictionary at <$> monoType element
  ("ord", [element]) -> orderDictionary at <$> monoType element
  ("monad", [_]) -> pure (unitType at)
  ("channel", [_]) -> pure (Located at (M.TFfi "Basis" "channel"))
  ("xml", [_, _, _]) -> pure (Located at (M.TFfi "Basis" "string"))
  ("xhtml", [_, _]) -> pure (Located at (M.TFfi "Basis" "string"))
  _
    | name `elem` erasedRecordApplications -> pure (unitType at)
    | name `elem` erasedStringApplications -> pure (Located at (M.TFfi "Basis" "string"))
    | otherwise -> pure (Located at (M.TFfi "Basis" name))
appliedFfiType at moduleName name _ = pure (Located at (M.TFfi moduleName name))

monoDatatypeType :: C.Con -> C.GlobalId -> [C.Con] -> MonoM M.Type
monoDatatypeType source identifier arguments = do
  state <- get
  case Map.lookup identifier (monoDatatypes state) of
    Nothing -> monoFailure source "unknown-datatype" "Named runtime type has no datatype declaration"
    Just definition
      | not (null (datatypeParameters definition)) ->
          monoFailure source "polymorphic-datatype-late"
            ("Polymorphic datatype " <> datatypeName definition <> " survived Core Specialize")
      | not (null arguments) ->
          monoFailure source "datatype-arity"
            ("Datatype " <> datatypeName definition <> " expects "
              <> show (length (datatypeParameters definition)) <> " static argument(s), but received "
              <> show (length arguments))
      | otherwise -> do
          instance' <- requestDatatype (locatedSpan source) identifier (map Substitute.normalizeCon arguments) definition
          pure (Located (locatedSpan source) (M.TDatatype (instanceTypeId instance')))

requestDatatype :: Span -> C.GlobalId -> [C.Con] -> DatatypeDef -> MonoM DatatypeInstance
requestDatatype at sourceId arguments definition = do
  state <- get
  reducedArguments <- mapM (expandAliases Set.empty . Substitute.normalizeCon) arguments
  let key = (sourceId, map Substitute.semanticCon reducedArguments)
  case Map.lookup key (monoInstances state) of
    Just instance' -> pure instance'
    Nothing -> do
      let typeId = M.GlobalId (monoNextId state)
          constructorIds = zipWith (\(_, old, _) offset -> (old, M.GlobalId (monoNextId state + offset + 1))) (datatypeConstructors definition) [0 ..]
          instance' = DatatypeInstance typeId (Map.fromList constructorIds)
      modify' $ \current ->
        current
          { monoNextId = monoNextId current + 1 + length constructorIds
          , monoInstances = Map.insert key instance' (monoInstances current)
          }
      constructors <- mapM (instantiateConstructor reducedArguments instance') (datatypeConstructors definition)
      let suffix = if null arguments then "" else "$mono"
          generated = Located at (M.DDatatype [(datatypeName definition <> suffix, typeId, constructors)])
      modify' $ \current -> current {monoGeneratedDatatypes = generated : monoGeneratedDatatypes current}
      pure instance'

instantiateConstructor
  :: [C.Con]
  -> DatatypeInstance
  -> (String, C.GlobalId, Maybe C.Con)
  -> MonoM (String, M.GlobalId, Maybe M.Type)
instantiateConstructor arguments instance' (name, oldId, payload) = do
  identifier <- case Map.lookup oldId (instanceConstructors instance') of
    Just found -> pure found
    Nothing -> monoFailureAt "datatype-constructor" "Missing constructor in datatype instance"
  payload' <- traverse (monoType . instantiateParameters arguments) payload
  pure (name, identifier, payload')

instantiateParameters :: [C.Con] -> C.Con -> C.Con
instantiateParameters arguments body = foldl (flip (Substitute.substituteCon 0)) body (reverse arguments)

monoPatCon :: C.PatCon -> [C.Con] -> MonoM M.PatCon
monoPatCon constructor arguments = case constructor of
  C.PConFfi moduleName datatypeName _ name payload _ ->
    M.PConFfi moduleName datatypeName name <$> traverse (monoType . instantiateParameters arguments) payload
  C.PConVar oldId -> do
    state <- get
    case Map.lookup oldId (monoConstructorParents state) of
      Nothing -> pure (M.PConVar oldId)
      Just parent -> case Map.lookup parent (monoDatatypes state) of
        Nothing -> pure (M.PConVar oldId)
        Just definition -> do
          if not (null (datatypeParameters definition))
            then monoFailureAt "polymorphic-datatype-late" ("Polymorphic datatype " <> datatypeName definition <> " survived Core Specialize")
            else if not (null arguments)
              then monoFailureAt "datatype-arity" "A parameter-free datatype constructor retained static arguments"
              else do
                instance' <- requestDatatype (maybeSpan arguments) parent [] definition
                case Map.lookup oldId (instanceConstructors instance') of
                  Just identifier -> pure (M.PConVar identifier)
                  Nothing -> monoFailureAt "datatype-constructor" "Constructor is absent from its datatype instance"
  where
    maybeSpan (first : _) = locatedSpan first
    maybeSpan [] = errorSpan

monoStaticArg :: C.Con -> MonoM M.StaticArg
monoStaticArg = staticArg 0

staticArg :: Int -> C.Con -> MonoM M.StaticArg
staticArg depth source = do
  normalized <- expandAliases Set.empty (Substitute.normalizeCon source)
  case locatedValue normalized of
    C.CName name -> pure (M.StaticName name)
    C.CRecord _ fields -> M.StaticRow <$> mapM staticField fields
    C.CTuple elements -> M.StaticTuple <$> mapM go elements
    C.CUnit -> pure M.StaticUnit
    C.CMap {} -> pure M.StaticMap
    C.CRel index
      | index < depth -> pure (M.StaticBound index)
      | otherwise -> monoFailure source "open-static-argument" "Open constructor reached a runtime intrinsic"
    C.CAbs _ _ body -> M.StaticLambda <$> staticArg (depth + 1) body
    C.CProj tuple index -> M.StaticProject <$> go tuple <*> pure index
    C.CConcat left right -> M.StaticConcat <$> go left <*> go right
    C.CFfi moduleName name -> pure (M.StaticFfi moduleName name [])
    C.CApp {} -> do
      let (headConstructor, arguments) = collectApplications normalized
      head' <- expandAliases Set.empty headConstructor
      case locatedValue head' of
        C.CFfi moduleName name -> M.StaticFfi moduleName name <$> mapM go arguments
        _ -> foldl M.StaticApply <$> go head' <*> mapM go arguments
    _ -> M.StaticType <$> monoType normalized
  where
    go = staticArg depth
    staticField (name, value) = (,) <$> go name <*> go value

monoName :: C.Con -> MonoM String
monoName source = do
  normalized <- expandAliases Set.empty (Substitute.normalizeCon source)
  case locatedValue normalized of
    C.CName name -> pure name
    _ -> monoFailure source "mono-name" "Record label did not normalize to a concrete name"

expandAliases :: Set C.GlobalId -> C.Con -> MonoM C.Con
expandAliases seen constructor = case locatedValue constructor of
  C.CNamed identifier -> do
    state <- get
    case Map.lookup identifier (monoAliases state) of
      Just definition | Set.notMember identifier seen -> expandAliases (Set.insert identifier seen) (Substitute.normalizeCon definition)
      _ -> pure constructor
  C.CApp function argument -> do
    function' <- expandAliases seen function
    pure (Substitute.normalizeCon constructor {locatedValue = C.CApp function' argument})
  _ -> pure constructor

collectApplications :: C.Con -> (C.Con, [C.Con])
collectApplications constructor = case locatedValue constructor of
  C.CApp function argument -> let (headConstructor, arguments) = collectApplications function in (headConstructor, arguments <> [argument])
  _ -> (constructor, [])

unitType :: Span -> M.Type
unitType at = Located at (M.TRecord [])

function2 :: Span -> M.Type -> M.Type -> M.Type -> M.Type
function2 at first second result = Located at (M.TFun first (Located at (M.TFun second result)))

numericDictionary :: Span -> M.Type -> M.Type
numericDictionary at typ = Located at (M.TRecord
  [ ("Zero", typ)
  , ("Neg", Located at (M.TFun typ typ))
  , ("Plus", function2 at typ typ typ)
  , ("Minus", function2 at typ typ typ)
  , ("Times", function2 at typ typ typ)
  , ("Div", function2 at typ typ typ)
  , ("Mod", function2 at typ typ typ)
  , ("Pow", function2 at typ typ typ)
  ])

orderDictionary :: Span -> M.Type -> M.Type
orderDictionary at typ = Located at (M.TRecord
  [ ("Lt", function2 at typ typ bool)
  , ("Le", function2 at typ typ bool)
  ])
  where bool = Located at (M.TFfi "Basis" "bool")

readDictionary :: Span -> M.Type -> M.Type
readDictionary at typ = Located at (M.TRecord
  [ ("Read", Located at (M.TFun string (Located at (M.TOption typ))))
  , ("ReadError", Located at (M.TFun string typ))
  ])
  where string = Located at (M.TFfi "Basis" "string")

classify :: [(String, identifier, Maybe typ)] -> C.DatatypeKind
classify constructors
  | all noPayload constructors = C.Enum
  | length constructors == 2 && length (filter noPayload constructors) == 1 = C.Option
  | otherwise = C.Default
  where noPayload (_, _, payload) = case payload of Nothing -> True; Just _ -> False

stringLikeTypes :: [String]
stringLikeTypes =
  [ "page", "xhead", "xbody", "xtable", "xtr", "xform", "url", "mimeType"
  , "css_class", "css_value", "css_property", "css_style", "id", "requestHeader"
  , "responseHeader", "envVar", "meta", "data_attr_kind", "data_attr"
  ]

erasedRecordApplications :: [String]
erasedRecordApplications =
  [ "monad", "sql_window", "linkable", "sql_subset", "fieldsOf", "nullify"
  , "sql_summable", "sql_maxable", "sql_arith", "trigrammable"
  ]

erasedStringApplications :: [String]
erasedStringApplications =
  [ "serialized", "http_cookie", "sql_table", "sql_view", "sql_query", "sql_query1"
  , "sql_from_items", "sql_exp", "sql_expw", "sql_window_function", "primary_key"
  , "sql_constraints", "sql_constraint", "propagation_mode", "sql_order_by"
  , "sql_injectable_prim", "sql_injectable", "sql_unary", "sql_binary"
  , "sql_aggregate", "sql_nfunc", "sql_ufunc", "sql_bfunc", "sql_partition"
  ]

monoFailure :: Located source -> String -> String -> MonoM value
monoFailure source code message = StateT (const (Left (diagnostic MonoPhase code (locatedSpan source) message)))

monoFailureAt :: String -> String -> MonoM value
monoFailureAt code message = StateT (const (Left (diagnostic MonoPhase code errorSpan message)))

errorSpan :: Span
errorSpan = noSpan
