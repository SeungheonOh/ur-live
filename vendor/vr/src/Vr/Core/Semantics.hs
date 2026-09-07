{-# LANGUAGE DerivingStrategies #-}

-- | Whole-program semantic checks and export effect inference that must run
-- after Core specialization but before any backend sees the program.
module Vr.Core.Semantics
  ( SemanticSettings (..)
  , defaultSemanticSettings
  , checkAndEffectize
  ) where

import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Vr.Core.Syntax as C
import Vr.Middle (Effect (..), ExportKind (..))
import Vr.Source
  ( Diagnostic
  , DiagnosticPhase (CorePhase)
  , Located (..)
  , diagnostic
  )

type ForeignName = (String, String)

data SemanticSettings = SemanticSettings
  { semanticClientToServer :: !(Set.Set ForeignName)
  , semanticEffectful :: !(Set.Set ForeignName)
  , semanticBenignEffectful :: !(Set.Set ForeignName)
  , semanticClientOnly :: !(Set.Set ForeignName)
  , semanticServerOnly :: !(Set.Set ForeignName)
  , semanticSafeGetDefault :: !Bool
  , semanticSafeGets :: !(Set.Set String)
  }
  deriving stock (Eq, Show)

defaultSemanticSettings :: SemanticSettings
defaultSemanticSettings = SemanticSettings
  { semanticClientToServer = Set.fromList
      [("Basis", name) | name <-
        ["int", "float", "string", "char", "time", "file", "unit", "option", "list", "bool", "variant"]]
  , semanticEffectful = Set.fromList
      [("Basis", name) | name <-
        [ "dml", "nextval", "setval", "set_cookie", "clear_cookie", "new_channel", "send"
        , "htmlifyInt_w", "htmlifyFloat_w", "htmlifyString_w", "htmlifyBool_w", "htmlifyTime_w"
        , "attrifyInt_w", "attrifyFloat_w", "attrifyString_w", "attrifyChar_w"
        , "urlifyInt_w", "urlifyFloat_w", "urlifyString_w", "urlifyBool_w", "urlifyChannel_w"
        ]]
  , semanticBenignEffectful = Set.fromList
      [("Basis", name) | name <-
        [ "get_cookie", "getenv", "new_client_source", "get_client_source", "set_client_source"
        , "current", "alert", "confirm", "onError", "onFail", "onConnectFail"
        , "onDisconnect", "onServerError", "mouseEvent", "keyEvent", "debug", "rand", "now"
        , "getHeader", "setHeader", "spawn", "onClick", "onDblclick", "onContextmenu"
        , "onKeydown", "onKeypress", "onKeyup", "onMousedown", "onMouseenter"
        , "onMouseleave", "onMousemove", "onMouseout", "onMouseover", "onMouseup"
        , "preventDefault", "stopPropagation", "fresh", "giveFocus"
        , "currentUrlHasPost", "currentUrlHasQueryString", "currentUrl"
        ]]
  , semanticClientOnly = Set.fromList
      [("Basis", name) | name <-
        [ "get_client_source", "current", "alert", "confirm", "recv", "sleep", "spawn"
        , "onError", "onFail", "onConnectFail", "onDisconnect", "onServerError"
        , "mouseEvent", "keyEvent", "onClick", "onContextmenu", "onDblclick"
        , "onKeydown", "onKeypress", "onKeyup", "onMousedown", "onMouseenter"
        , "onMouseleave", "onMousemove", "onMouseout", "onMouseover", "onMouseup"
        , "preventDefault", "stopPropagation", "giveFocus"
        ]]
  , semanticServerOnly = Set.fromList
      [("Basis", name) | name <-
        [ "requestHeader", "query", "dml", "nextval", "setval", "channel", "send"
        , "fieldName", "fieldValue", "remainingFields", "firstFormField"
        ]]
  , semanticSafeGetDefault = False
  , semanticSafeGets = Set.empty
  }

checkAndEffectize :: SemanticSettings -> C.File -> Either [Diagnostic] C.File
checkAndEffectize settings file =
  let marshalProblems = checkMarshalling settings file
      (effectProblems, effected) = effectize settings file
      problems = marshalProblems <> effectProblems
   in if null problems then Right effected else Left problems

-- MarshalCheck ---------------------------------------------------------------

checkMarshalling :: SemanticSettings -> C.File -> [Diagnostic]
checkMarshalling settings file = exportProblems <> cookieProblems <> expressionProblems
  where
    dependencies = closeTypeDependencies settings file
    valueTypes = Map.fromList (concatMap collectValueType file)
    forbidden typ = conForeignWith (semanticClientToServer settings) dependencies typ
    exportProblems = concat
      [ case Map.lookup identifier valueTypes of
          Nothing -> [at declaration "marshal-export" "Export target has no Core value type"]
          Just typ -> report declaration "page handler inputs" (handlerInputs forbidden typ)
      | declaration <- file
      , C.DExport _ identifier _ <- [locatedValue declaration]
      ]
    cookieProblems = concat
      [ report declaration ("cookie '" <> physicalName <> "'") (forbidden typ)
      | declaration <- file
      , C.DCookie _ _ typ physicalName <- [locatedValue declaration]
      ]
    expressionProblems = concatMap (declarationExpressionProblems forbidden) file
    report declaration subject names
      | Set.null names = []
      | otherwise = [at declaration "marshal-type"
          ("Not allowed to serialize " <> subject <> " involving " <> renderNames names)]
    at source code message = diagnostic CorePhase code (locatedSpan source) message

handlerInputs :: (C.Con -> Set.Set ForeignName) -> C.Con -> Set.Set ForeignName
handlerInputs forbidden typ = case locatedValue typ of
  C.TFun domain range
    | isPostBody domain || isOptionalQueryString domain -> handlerInputs forbidden range
    | otherwise -> forbidden domain <> handlerInputs forbidden range
  _ -> Set.empty

isPostBody :: C.Con -> Bool
isPostBody typ = case locatedValue typ of
  C.CFfi "Basis" "postBody" -> True
  _ -> False

isOptionalQueryString :: C.Con -> Bool
isOptionalQueryString typ = case locatedValue typ of
  C.CApp option query -> isFfi "Basis" "option" option && isFfi "Basis" "queryString" query
  _ -> False

declarationExpressionProblems :: (C.Con -> Set.Set ForeignName) -> C.Decl -> [Diagnostic]
declarationExpressionProblems forbidden declaration = concatMap inspect (declExpressions declaration)
  where
    inspect = expressionFold $ \expression children -> case locatedValue expression of
      C.ECApp function typ | isSerializationHead function -> typeProblem expression typ <> children
      _ -> children
    typeProblem source typ = case forbidden typ of
      names | Set.null names -> []
      names -> [diagnostic CorePhase "marshal-type" (locatedSpan source)
        ("Not allowed to [de]serialize a value involving " <> renderNames names)]

isSerializationHead :: C.Expr -> Bool
isSerializationHead expression = case locatedValue expression of
  C.EFfi "Basis" name -> name == "serialize" || name == "deserialize"
  _ -> False

closeTypeDependencies :: SemanticSettings -> C.File -> Map.Map C.GlobalId (Set.Set ForeignName)
closeTypeDependencies settings file = close initial
  where
    definitions = Map.fromList (concatMap collectDefinitions file)
    initial = Map.map (const Set.empty) definitions
    close known =
      let next = Map.map (Set.unions . map (conForeign known)) definitions
       in if next == known then known else close next
    collectDefinitions declaration = case locatedValue declaration of
      C.DCon _ identifier _ body -> [(identifier, [body])]
      C.DDatatype definitions' ->
        [(identifier, [payload | (_, _, Just payload) <- constructors]) | (_, identifier, _, constructors) <- definitions']
      _ -> []
    allowed = semanticClientToServer settings
    -- This local binding ensures custom whitelist entries are used even for
    -- direct FFI nodes while the fixed point follows named constructors.
    conForeign known = conForeignWith allowed known

conForeignWith
  :: Set.Set ForeignName
  -> Map.Map C.GlobalId (Set.Set ForeignName)
  -> C.Con
  -> Set.Set ForeignName
conForeignWith allowed known typ = direct <> Set.unions (map recur (conChildren typ))
  where
    recur = conForeignWith allowed known
    direct = case locatedValue typ of
      C.CFfi moduleName name
        | Set.member (moduleName, name) allowed -> Set.empty
        | otherwise -> Set.singleton (moduleName, name)
      C.CNamed identifier -> Map.findWithDefault Set.empty identifier known
      _ -> Set.empty

conChildren :: C.Con -> [C.Con]
conChildren typ = case locatedValue typ of
  C.TFun domain range -> [domain, range]
  C.TCFun _ _ body -> [body]
  C.TRecord row -> [row]
  C.CApp function argument -> [function, argument]
  C.CAbs _ _ body -> [body]
  C.CKAbs _ body -> [body]
  C.CKApp function _ -> [function]
  C.TKFun _ body -> [body]
  C.CRecord _ fields -> concat [[name, value] | (name, value) <- fields]
  C.CConcat left right -> [left, right]
  C.CTuple elements -> elements
  C.CProj tuple _ -> [tuple]
  _ -> []

renderNames :: Set.Set ForeignName -> String
renderNames names = unwords
  [moduleName <> "." <> name | (moduleName, name) <- Set.toAscList names]

-- Effectize ------------------------------------------------------------------

effectize :: SemanticSettings -> C.File -> ([Diagnostic], C.File)
effectize settings file = (problems, map rewrite file)
  where
    values = Map.fromList (concatMap collectValue file)
    writers = fixedPoint (couldWrite settings) values
    readers = fixedPoint couldRead values
    pushers = fixedPoint (couldPush writers readers) values
    paths = Map.fromList
      [(identifier, path) | (identifier, (_, _, path)) <- Map.toList values]
    problems =
      [ diagnostic CorePhase "unsafe-get" (locatedSpan declaration)
          ("A handler (URI prefix '" <> Map.findWithDefault "" identifier paths
            <> "') accessible via GET could cause side effects; use a form or whitelist it with safeGet")
      | declaration <- file
      , C.DExport (Link _) identifier _ <- [locatedValue declaration]
      , Set.member identifier writers
      , not (safeGet identifier)
      ]
    safeGet identifier = semanticSafeGetDefault settings
      || Set.member (Map.findWithDefault "" identifier paths) (semanticSafeGets settings)
    rewrite declaration = declaration {locatedValue = case locatedValue declaration of
      C.DExport kind identifier _ -> C.DExport (withEffect kind (effect identifier)) identifier (Set.member identifier pushers)
      other -> other}
    effect identifier
      | Set.member identifier writers && Set.member identifier readers = ReadCookieWrite
      | Set.member identifier writers = ReadWrite
      | otherwise = ReadOnly

type ValueMap = Map.Map C.GlobalId (C.Expr, Located C.DeclF, String)

collectValue :: C.Decl -> [(C.GlobalId, (C.Expr, Located C.DeclF, String))]
collectValue declaration = case locatedValue declaration of
  C.DVal _ identifier _ expression path -> [(identifier, (expression, declaration, path))]
  C.DValRec bindings ->
    [(identifier, (expression, declaration, path)) | (_, identifier, _, expression, path) <- bindings]
  _ -> []

collectValueType :: C.Decl -> [(C.GlobalId, C.Con)]
collectValueType declaration = case locatedValue declaration of
  C.DVal _ identifier typ _ _ -> [(identifier, typ)]
  C.DValRec bindings -> [(identifier, typ) | (_, identifier, typ, _, _) <- bindings]
  _ -> []

fixedPoint
  :: (Set.Set C.GlobalId -> C.Expr -> Bool)
  -> ValueMap
  -> Set.Set C.GlobalId
fixedPoint predicate values = go Set.empty
  where
    go known =
      let next = known <> Set.fromList
            [identifier | (identifier, (expression, _, _)) <- Map.toList values, predicate known expression]
       in if next == known then known else go next

couldWrite :: SemanticSettings -> Set.Set C.GlobalId -> C.Expr -> Bool
couldWrite settings writers = expressionAnyWithChildren serverEffectChildren node
  where
    node expression = case locatedValue expression of
      C.EFfi moduleName name -> effectful (moduleName, name)
      C.EFfiApp moduleName name _ -> effectful (moduleName, name)
      C.ENamed identifier -> Set.member identifier writers
      C.ERecord fields -> any onloadWrites
        [value | (name, value, _) <- fields, constructorName name == Just "Onload"]
      _ -> False
    effectful name = Set.member name (semanticEffectful settings)
      && not (Set.member name (semanticClientOnly settings))
    -- Effectize treats Onload specially: unlike the other browser event
    -- islands, an RPC reached from Onload contributes the target handler's
    -- write effect to the page that installs it.
    onloadWrites = expressionAny onloadNode
    onloadNode expression = case locatedValue expression of
      C.EFfi moduleName name -> effectful (moduleName, name)
      C.EFfiApp moduleName name _ -> effectful (moduleName, name)
      C.ENamed identifier -> Set.member identifier writers
      C.EServerCall identifier _ _ _ -> Set.member identifier writers
      _ -> False

couldRead :: Set.Set C.GlobalId -> C.Expr -> Bool
couldRead readers = expressionAnyWithChildren serverEffectChildren node
  where
    node expression = case locatedValue expression of
      C.EFfi "Basis" "getCookie" -> True
      C.EFfiApp "Basis" name _ -> name == "getHeader" || name == "getenv"
      C.ENamed identifier -> Set.member identifier readers
      C.EServerCall identifier _ _ _ -> Set.member identifier readers
      _ -> False

-- Effectize removes ordinary browser event attributes before computing both
-- read and write effects.  Onload is intentionally retained because it runs
-- automatically when the page is installed.
serverEffectChildren :: C.Expr -> [C.Expr]
serverEffectChildren expression = case locatedValue expression of
  C.ERecord fields ->
    [value | (name, value, _) <- fields, maybe True keep (constructorName name)]
  _ -> expressionChildren expression
  where
    keep name = name == "Onload" || not ("On" `isPrefixOf` name)

couldPush
  :: Set.Set C.GlobalId
  -> Set.Set C.GlobalId
  -> Set.Set C.GlobalId
  -> C.Expr
  -> Bool
couldPush writers readers pushers = expressionAny node
  where
    node expression = case locatedValue expression of
      C.ENamed identifier -> Set.member identifier pushers
      C.EServerCall identifier _ _ _ -> Set.member identifier writers && Set.member identifier readers
      _ -> False

withEffect :: ExportKind -> Effect -> ExportKind
withEffect kind effect = case kind of
  Link _ -> Link effect
  Action _ -> Action effect
  Rpc _ -> Rpc effect
  Extern _ -> Extern effect

constructorName :: C.Con -> Maybe String
constructorName constructor = case locatedValue constructor of
  C.CName name -> Just name
  _ -> Nothing

declExpressions :: C.Decl -> [C.Expr]
declExpressions declaration = case locatedValue declaration of
  C.DVal _ _ _ expression _ -> [expression]
  C.DValRec bindings -> [expression | (_, _, _, expression, _) <- bindings]
  C.DTable _ _ _ _ primary _ constraints _ -> [primary, constraints]
  C.DView _ _ _ expression _ -> [expression]
  C.DIndex table modes -> [table, modes]
  C.DTask schedule body -> [schedule, body]
  C.DPolicy expression -> [expression]
  _ -> []

expressionAny :: (C.Expr -> Bool) -> C.Expr -> Bool
expressionAny predicate = expressionAnyWithChildren expressionChildren predicate

expressionAnyWithChildren
  :: (C.Expr -> [C.Expr])
  -> (C.Expr -> Bool)
  -> C.Expr
  -> Bool
expressionAnyWithChildren children predicate expression =
  predicate expression || any (expressionAnyWithChildren children predicate) (children expression)

expressionFold :: Monoid value => (C.Expr -> value -> value) -> C.Expr -> value
expressionFold step expression = step expression (foldMap (expressionFold step) (expressionChildren expression))

expressionChildren :: C.Expr -> [C.Expr]
expressionChildren expression = case locatedValue expression of
  C.ECon _ _ _ payload -> maybe [] pure payload
  C.EFfiApp _ _ arguments -> map fst arguments
  C.EApp function argument -> [function, argument]
  C.EAbs _ _ _ body -> [body]
  C.ECApp function _ -> [function]
  C.ECAbs _ _ body -> [body]
  C.EKAbs _ body -> [body]
  C.EKApp function _ -> [function]
  C.ERecord fields -> [value | (_, value, _) <- fields]
  C.EField record _ _ _ -> [record]
  C.EConcat left _ right _ -> [left, right]
  C.ECut record _ _ _ -> [record]
  C.ECutMulti record _ _ -> [record]
  C.ECase scrutinee branches _ _ -> scrutinee : map snd branches
  C.EWrite value -> [value]
  C.EClosure _ captures -> captures
  C.ELet _ _ value body -> [value, body]
  C.EServerCall _ arguments _ _ -> arguments
  _ -> []

isFfi :: String -> String -> C.Con -> Bool
isFfi moduleName name typ = case locatedValue typ of
  C.CFfi moduleName' name' -> moduleName == moduleName' && name == name'
  _ -> False
