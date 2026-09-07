{-# LANGUAGE TupleSections #-}

-- | Evaluate Explicit structures and functors and emit a single module-free
-- Core program.  This pass deliberately stops before any target-specific
-- choice: SQL, browser/server placement, JavaScript, and LLVM remain concerns
-- of Mono and its future consumers.
module Vr.Core.Corify
  ( corifyFile
  , corifyFileWithRewrites
  ) where

import Data.Char (isAlphaNum)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Vr.Core.Corify.Convert as Convert
import qualified Vr.Core.Corify.State as State
import qualified Vr.Core.Syntax as C
import qualified Vr.Explicit.Syntax as E
import Vr.Middle (Effect (ReadCookieWrite), ExportKind (Extern, Link))
import Vr.Project
  ( PathKind (..)
  , RewriteRule
  , rewriteProjectPath
  )
import Vr.Source (Diagnostic, DiagnosticPhase (CorePhase), Located (..), Span, diagnostic)

corifyFile :: E.File -> Either [Diagnostic] C.File
corifyFile = corifyFileWithRewrites []

-- | Flatten modules while applying the project's public-name rewrites at the
-- same point as Ur/Web's Corify pass.  This ensures handler URLs, relation
-- names, cookies, and styles agree before tagging and duplicate-path checks.
corifyFileWithRewrites :: [RewriteRule] -> E.File -> Either [Diagnostic] C.File
corifyFileWithRewrites rewrites file = case corifyDeclarations rewrites [] file (State.initialState (maximumGlobal file + 1)) of
  Left problem -> Left [problem]
  Right (declarations, _) -> Right declarations

corifyDeclarations
  :: [RewriteRule]
  -> [String]
  -> [E.Decl]
  -> State.CorifyState
  -> Either Diagnostic ([C.Decl], State.CorifyState)
corifyDeclarations rewrites modules declarations state0 = foldlM step ([], state0) declarations
  where
    step (done, state) declaration = do
      (generated, state') <- corifyDeclaration rewrites modules declaration state
      pure (done <> generated, state')

corifyDeclaration
  :: [RewriteRule]
  -> [String]
  -> E.Decl
  -> State.CorifyState
  -> Either Diagnostic ([C.Decl], State.CorifyState)
corifyDeclaration rewrites modules declaration state0 = case locatedValue declaration of
  E.DCon name old kind definition -> do
    let (identifier, allocated) = State.bindCon name old state0
        state1 = State.bindConDefinition old definition allocated
    definition' <- Convert.corifyCon state1 definition
    pure ([at (C.DCon name identifier (Convert.corifyKind kind) definition')], state1)

  E.DDatatype definitions -> corifyDatatypes declaration definitions state0

  E.DDatatypeImp name old root path originalName parameters constructors -> do
    originalFlat <- Convert.resolveFlat state0 root path declaration
    let (identifier, state1) = State.bindCon name old state0
        projected = Located location (E.CModProj root path originalName)
    definition <- Convert.corifyCon state1 projected
    (constructorDecls, state2) <- foldlM (importConstructor root path originalFlat identifier parameters) ([], state1) constructors
    let kind = foldr (\_ result -> Located location (C.KArrow (Located location C.KType) result)) (Located location C.KType) parameters
    pure (at (C.DCon name identifier kind definition) : constructorDecls, state2)

  E.DVal name old typ expression -> do
    let stateAlias = case locatedValue expression of
          E.ENamed sourceId -> maybe state0 (\constructor -> State.bindConstructorAs name old constructor state0) (State.lookupConstructorId sourceId state0)
          _ -> state0
        (identifier, state1) = State.bindValue name old stateAlias
    typ' <- Convert.corifyCon state1 typ
    expression' <- Convert.corifyExpr state1 expression
    pure ([at (C.DVal name identifier typ' expression' (restName rewrites UrlPath modules name))], state1)

  E.DValRec bindings -> do
    let allocateBinding (done, state) (name, old, typ, expression) =
          let (identifier, state') = State.bindValue name old state
           in (done <> [(name, identifier, typ, expression)], state')
        (allocated, state1) = foldl' allocateBinding ([], state0) bindings
    bindings' <- mapM (corifyRecursiveBinding rewrites modules state1) allocated
    pure ([at (C.DValRec bindings')], state1)

  E.DSgn {} -> pure ([], state0)

  E.DStr name old signature structure -> case locatedValue structure of
    E.StrFun parameter parameterId _ _ body ->
      pure ([], State.bindFunctor name old (State.FunctorBinding parameter parameterId body) state0)
    E.StrVar identifier -> case State.lookupFunctorId identifier state0 of
      Just functor -> pure ([], State.bindFunctor name old functor state0)
      Nothing -> ordinaryStructure name old signature structure
    E.StrProj parent field -> case resolveStructureOnly parent state0 of
      Right flat -> case State.lookupFunctorName field flat of
        Just functor -> pure ([], State.bindFunctor name old functor state0)
        Nothing -> ordinaryStructure name old signature structure
      Left _ -> ordinaryStructure name old signature structure
    _ -> ordinaryStructure name old signature structure

  E.DFfiStr moduleName old signature -> corifyForeignStructure declaration moduleName old signature state0

  E.DExport _ signature structure -> corifyExport declaration signature structure state0

  E.DTable _ name old row primary keys constraints uniques -> do
    let (identifier, state1) = State.bindValue name old state0
    row' <- Convert.corifyCon state1 row
    primary' <- Convert.corifyExpr state1 primary
    keys' <- Convert.corifyCon state1 keys
    constraints' <- Convert.corifyExpr state1 constraints
    uniques' <- Convert.corifyCon state1 uniques
    pure ([at (C.DTable name identifier row' (sqlName rewrites TablePath modules name) primary' keys' constraints' uniques')], state1)

  E.DSequence _ name old ->
    let (identifier, state1) = State.bindValue name old state0
     in pure ([at (C.DSequence name identifier (sqlName rewrites SequencePath modules name))], state1)

  E.DView _ name old expression row -> do
    let (identifier, state1) = State.bindValue name old state0
    expression' <- Convert.corifyExpr state1 expression
    row' <- Convert.corifyCon state1 row
    pure ([at (C.DView name identifier (sqlName rewrites ViewPath modules name) expression' row')], state1)

  E.DIndex table modes -> do
    table' <- Convert.corifyExpr state0 table
    modes' <- Convert.corifyExpr state0 modes
    pure ([at (C.DIndex table' modes')], state0)

  E.DDatabase name -> pure ([at (C.DDatabase name)], state0)

  E.DCookie _ name old typ -> do
    let (identifier, state1) = State.bindValue name old state0
    typ' <- Convert.corifyCon state1 typ
    pure ([at (C.DCookie name identifier typ' (restName rewrites CookiePath modules name))], state1)

  E.DStyle _ name old ->
    let (identifier, state1) = State.bindValue name old state0
     in pure ([at (C.DStyle name identifier (sqlName rewrites StylePath modules name))], state1)

  E.DTask kind body -> do
    kind' <- Convert.corifyExpr state0 kind
    body' <- Convert.corifyExpr state0 body
    pure ([at (C.DTask kind' body')], state0)

  E.DPolicy expression -> do
    expression' <- Convert.corifyExpr state0 expression
    pure ([at (C.DPolicy expression')], state0)

  E.DOnError root path name -> do
    flat <- Convert.resolveFlat state0 root path declaration
    case State.lookupValueName name flat of
      Just (State.NormalValue identifier) -> pure ([at (C.DOnError identifier)], state0)
      _ -> failure declaration "on-error-target" "The onError target is not an Ur value"

  E.DFfi name old _ typ -> do
    moduleName <- case State.scopePath state0 of
      [single] -> pure single
      _ -> failure declaration "nested-ffi"
        "Used 'ffi' declaration beneath module top level"
    typ' <- Convert.corifyCon state0 typ
    let state1 = State.bindForeignValue name old moduleName typ' state0
    pure ([at (C.DForeign moduleName name typ')], state1)
  where
    location = locatedSpan declaration
    at = Located location
    ordinaryStructure name old signature structure = do
      let modules' = if name == "anon" then modules else name : modules
      (generated, inner, outer) <- corifyStructure rewrites modules' structure state0
      let withSignatureIds = bindSignatureAliases signature inner outer
      pure (generated, State.bindStructure name old inner withSignatureIds)
    importConstructor root path originalFlat datatypeId parameters (done, state) (name, old, payload) = do
      constructor <- case State.lookupConstructorName name originalFlat of
        Just found -> pure found
        Nothing -> failure declaration "imported-constructor" ("Imported datatype has no constructor " <> name)
      let state1 = State.bindConstructorAs name old constructor state
          (identifier, state2) = State.bindValue name old state1
      payload' <- traverse (Convert.corifyCon state2) payload
      let result = applyParameters location datatypeId parameters
          typ = maybe result (\domain -> Located location (C.TFun domain result)) payload'
          typ' = foldr (\parameter body -> Located location (C.TCFun parameter (Located location C.KType) body)) typ parameters
      expression <- Convert.corifyExpr state2 (Located location (E.EModProj root path name))
      pure (done <> [Located location (C.DVal name identifier typ' expression name)], state2)

corifyDatatypes
  :: E.Decl
  -> [(String, E.GlobalId, [String], [(String, E.GlobalId, Maybe E.Con)])]
  -> State.CorifyState
  -> Either Diagnostic ([C.Decl], State.CorifyState)
corifyDatatypes declaration definitions state0 = do
  let bindType (done, state) (name, old, parameters, constructors) =
        let (identifier, state') = State.bindCon name old state
         in (done <> [(name, identifier, parameters, constructors)], state')
      (typed, state1) = foldl' bindType ([], state0) definitions
  (coreDefinitions, constructorValues, state2) <- foldlM bindDefinition ([], [], state1) typed
  pure (Located location (C.DDatatype coreDefinitions) : reverse constructorValues, state2)
  where
    location = locatedSpan declaration
    bindDefinition (done, values, state) (name, identifier, parameters, constructors) = do
      let classification = classifyDatatype constructors
      (constructors', values', state') <- foldlM (bindOne classification identifier parameters) ([], [], state) constructors
      pure (done <> [(name, identifier, parameters, constructors')], values' <> values, state')
    bindOne classification datatypeId parameters (done, values, state) (name, old, payload) = do
      let (identifier, state1) = State.bindConstructor name old state
      payload' <- traverse (Convert.corifyCon state1) payload
      let result = applyParameters location datatypeId parameters
          arguments = [Located location (C.CRel index) | index <- reverse [0 .. length parameters - 1]]
          constructor = C.PConVar identifier
          (value, typ) = case payload' of
            Nothing -> (Located location (C.ECon classification constructor arguments Nothing), result)
            Just domain ->
              ( Located location (C.EAbs "x" domain result (Located location (C.ECon classification constructor arguments (Just (Located location (C.ERel 0))))))
              , Located location (C.TFun domain result)
              )
          value' = foldr (\parameter body -> Located location (C.ECAbs parameter (Located location C.KType) body)) value parameters
          typ' = foldr (\parameter body -> Located location (C.TCFun parameter (Located location C.KType) body)) typ parameters
          declaration' = Located location (C.DVal name identifier typ' value' "")
      pure (done <> [(name, identifier, payload')], declaration' : values, state1)

corifyRecursiveBinding
  :: [RewriteRule]
  -> [String]
  -> State.CorifyState
  -> (String, C.GlobalId, E.Con, E.Expr)
  -> Either Diagnostic (String, C.GlobalId, C.Con, C.Expr, String)
corifyRecursiveBinding rewrites modules state (name, identifier, typ, expression) =
  (,,,,) name identifier
    <$> Convert.corifyCon state typ
    <*> Convert.corifyExpr state expression
    <*> pure (restName rewrites UrlPath modules name)

corifyForeignStructure
  :: E.Decl
  -> String
  -> E.GlobalId
  -> E.Signature
  -> State.CorifyState
  -> Either Diagnostic ([C.Decl], State.CorifyState)
corifyForeignStructure declaration moduleName old signature state0 = case locatedValue signature of
  E.SgnConst items -> do
    (declarations, values, constructors, state1) <- foldlM step ([], Map.empty, Map.empty, state0) items
    let foreignFlat = State.makeForeign moduleName values constructors
        state2 = State.bindStructure moduleName old foreignFlat state1
        state3 = if moduleName == "Basis" then state2 {State.stateBasisId = Just old} else state2
    pure (declarations, state3)
  _ -> failure declaration "foreign-signature" "Foreign structures require a constant signature"
  where
    location = locatedSpan declaration
    step (done, values, constructors, state) item = case locatedValue item of
      E.SgiConAbs name oldCon kind -> foreignCon done values constructors state name oldCon kind Nothing
      E.SgiCon name oldCon kind definition -> foreignCon done values constructors state name oldCon kind (Just definition)
      E.SgiDatatype definitions -> foldlM foreignDatatype (done, values, constructors, state) definitions
      E.SgiDatatypeImp datatypeName oldType _ _ _ parameters dataConstructors ->
        foreignDatatype (done, values, constructors, state)
          (datatypeName, oldType, parameters, dataConstructors)
      E.SgiVal name oldValue typ -> do
        typ' <- Convert.corifyCon state typ
        let state' = State.aliasForeignValue oldValue moduleName name typ' state
            metadata =
              [Located (locatedSpan item) (C.DForeign moduleName name typ')
              | moduleName /= "Basis"]
        pure (done <> metadata, Map.insert name typ' values, constructors, state')
      E.SgiStr {} -> pure (done, values, constructors, state)
      E.SgiSgn {} -> pure (done, values, constructors, state)
    foreignCon done values constructors state name oldCon kind sourceDefinition =
      let (identifier, allocated) = State.bindCon name oldCon state
          withOrigin = State.markForeignCon oldCon moduleName name allocated
          state' = maybe withOrigin (\body -> State.bindConDefinition oldCon body withOrigin) sourceDefinition
          coreDefinition = Located location (C.CFfi moduleName name)
       in pure (done <> [Located location (C.DCon name identifier (Convert.corifyKind kind) coreDefinition)], values, constructors, state')
    foreignDatatype accumulator (datatypeName, oldType, parameters, dataConstructors) = do
      let (identifier, allocated) = State.bindCon datatypeName oldType (fourth accumulator)
          state1 = State.markForeignCon oldType moduleName datatypeName allocated
          kind = foldr (\_ result -> Located location (C.KArrow (Located location C.KType) result)) (Located location C.KType) parameters
          typeDeclaration = Located location (C.DCon datatypeName identifier kind (Located location (C.CFfi moduleName datatypeName)))
          classification = classifyDatatype dataConstructors
          (done0, values0, constructors0, _) = accumulator
      (done, values, constructors, state2) <- foldlM (foreignConstructor datatypeName parameters classification) (done0 <> [typeDeclaration], values0, constructors0, state1) dataConstructors
      pure (done, values, constructors, state2)
    foreignConstructor datatypeName parameters classification (done, values, constructors, state) (name, oldConstructor, payload) = do
      payload' <- traverse (Convert.corifyCon state) payload
      let constructor = C.PConFfi moduleName datatypeName parameters name payload' classification
          state1 = State.bindConstructorAs name oldConstructor constructor state
          (identifier, state2) = State.bindValue name oldConstructor state1
          datatypeType = foldl' (\function index -> Located location (C.CApp function (Located location (C.CRel index)))) (Located location (C.CFfi moduleName datatypeName)) (reverse [0 .. length parameters - 1])
          baseType = maybe datatypeType (\domain -> Located location (C.TFun domain datatypeType)) payload'
          typ = foldr (\parameter body -> Located location (C.TCFun parameter (Located location C.KType) body)) baseType parameters
          args = [Located location (C.CRel index) | index <- [0 .. length parameters - 1]]
          baseValue = case payload' of
            Nothing -> Located location (C.ECon classification constructor args Nothing)
            Just domain -> Located location (C.EAbs "x" domain datatypeType (Located location (C.ECon classification constructor args (Just (Located location (C.ERel 0))))))
          value = foldr (\parameter body -> Located location (C.ECAbs parameter (Located location C.KType) body)) baseValue parameters
          decl = Located location (C.DVal name identifier typ value "")
      pure (done <> [decl], Map.insert name typ values, Map.insert name constructor constructors, state2)
    fourth (_, _, _, value) = value

corifyExport
  :: E.Decl
  -> E.Signature
  -> E.Structure
  -> State.CorifyState
  -> Either Diagnostic ([C.Decl], State.CorifyState)
corifyExport declaration signature structure state = do
  flat <- resolveStructurePath declaration structure state
  items <- case locatedValue signature of
    E.SgnConst values -> pure values
    _ -> failure declaration "export-signature" "Export requires a constant signature"
  case
    [ item
    | item <- items
    , E.SgiVal ('?' : _) _ typ <- [locatedValue item]
    , isPageType state typ
    ] of
    hidden : _ -> failure hidden "shadowed-page-export"
      "A page-valued top-level declaration was shadowed before project export"
    [] -> pure ()
  let exports = mapMaybe (exportItem flat) items
  pure (exports, state)
  where
    exportItem flat item = case locatedValue item of
      E.SgiVal name _ typ | isPageType state typ -> case State.lookupValueName name flat of
        Just (State.NormalValue identifier) ->
          let kind = if containsPostBody state typ then Extern ReadCookieWrite else Link ReadCookieWrite
           in Just (Located (locatedSpan declaration) (C.DExport kind identifier False))
        _ -> Nothing
      _ -> Nothing

resolveStructurePath :: E.Decl -> E.Structure -> State.CorifyState -> Either Diagnostic State.Flat
resolveStructurePath source structure state = case locatedValue structure of
  E.StrVar identifier -> maybe missing pure (State.lookupStructureId identifier state)
  E.StrProj parent name -> do
    flat <- resolveStructurePath source parent state
    maybe missing pure (State.lookupStructureName name flat)
  _ -> failure source "export-structure" "Only a structure path can be exported"
  where missing = failure source "export-structure" "Unknown exported structure path"

corifyStructure
  :: [RewriteRule]
  -> [String]
  -> E.Structure
  -> State.CorifyState
  -> Either Diagnostic ([C.Decl], State.Flat, State.CorifyState)
corifyStructure rewrites modules structure state0 = case locatedValue structure of
  E.StrConst declarations -> do
    let state1 = State.enter modules state0
    (generated, state2) <- corifyDeclarations rewrites modules declarations state1
    case State.leave state2 of
      Just (inner, outer) -> pure (generated, inner, outer)
      Nothing -> failure structure "structure-stack" "Internal structure stack underflow"
  E.StrVar identifier -> case State.lookupStructureId identifier state0 of
    Just inner -> pure ([], inner, state0)
    Nothing -> failure structure "unknown-structure" "Unknown structure identity"
  E.StrProj parent name -> do
    (generated, inner, outer) <- corifyStructure rewrites modules parent state0
    case State.lookupStructureName name inner of
      Just projected -> pure (generated, projected, outer)
      Nothing -> failure structure "unknown-structure-field" ("Structure has no field " <> name)
  E.StrFun {} -> failure structure "nested-functor" "Nested functor reached structure evaluation"
  E.StrApp function argument -> do
    functor <- resolveFunctor structure function state0
    (argumentDeclarations, argumentFlat, outer1) <- corifyStructure rewrites modules argument state0
    let withParameter = State.bindStructure (State.functorParameterName functor) (State.functorParameterId functor) argumentFlat outer1
    (bodyDeclarations, bodyFlat, outer2) <- corifyStructure rewrites modules (State.functorBody functor) withParameter
    let closedBody = State.insertStructure (State.functorParameterName functor) argumentFlat bodyFlat
    pure (argumentDeclarations <> bodyDeclarations, closedBody, outer2)

resolveFunctor :: E.Structure -> E.Structure -> State.CorifyState -> Either Diagnostic State.FunctorBinding
resolveFunctor source structure state = case locatedValue structure of
  E.StrVar identifier -> maybe missing pure (State.lookupFunctorId identifier state)
  E.StrProj parent name -> do
    flat <- resolveStructureOnly parent state
    maybe missing pure (State.lookupFunctorName name flat)
  _ -> failure source "functor-expression" "Functor application requires a structure path"
  where missing = failure source "unknown-functor" "Unknown functor identity"

resolveStructureOnly :: E.Structure -> State.CorifyState -> Either Diagnostic State.Flat
resolveStructureOnly structure state = case locatedValue structure of
  E.StrVar identifier -> maybe missing pure (State.lookupStructureId identifier state)
  E.StrProj parent name -> do
    flat <- resolveStructureOnly parent state
    maybe missing pure (State.lookupStructureName name flat)
  _ -> failure structure "structure-path" "Expected a structure path"
  where missing = failure structure "unknown-structure" "Unknown structure path"

-- A checked implementation and its public signature may use different
-- nominal IDs.  Client expressions refer to the signature IDs, so after a
-- structure body is flattened we alias every public identity to the concrete
-- component selected by its name.
bindSignatureAliases :: E.Signature -> State.Flat -> State.CorifyState -> State.CorifyState
bindSignatureAliases signature flat state = case locatedValue signature of
  E.SgnConst items -> foldl' bindItem state items
  E.SgnWhere base _ _ _ -> bindSignatureAliases base flat state
  _ -> state
  where
    bindItem current item = case locatedValue item of
      E.SgiConAbs name identifier _ -> maybe current (\target -> bindConTarget identifier target current) (State.lookupConName name flat)
      E.SgiCon name identifier _ _ -> maybe current (\target -> bindConTarget identifier target current) (State.lookupConName name flat)
      E.SgiDatatype definitions -> foldl' bindDatatype current definitions
      E.SgiDatatypeImp name identifier _ _ _ _ constructors ->
        let withType = maybe current (\target -> bindConTarget identifier target current) (State.lookupConName name flat)
         in foldl' bindConstructor withType constructors
      E.SgiVal name identifier _ -> case State.lookupValueName name flat of
        Just target -> State.aliasValue identifier target current
        Nothing -> current
      E.SgiStr name identifier nested -> case State.lookupStructureName name flat of
        Just nestedFlat -> bindSignatureAliases nested nestedFlat (State.aliasStructure identifier nestedFlat current)
        Nothing -> case State.lookupFunctorName name flat of
          Just functor -> State.aliasFunctor identifier functor current
          Nothing -> current
      E.SgiSgn {} -> current
    bindDatatype current (name, identifier, _, constructors) =
      let withType = maybe current (\target -> bindConTarget identifier target current) (State.lookupConName name flat)
       in foldl' bindConstructor withType constructors
    bindConstructor current (name, identifier, _) = case State.lookupConstructorName name flat of
      Just target -> State.aliasConstructor identifier target current
      Nothing -> current
    bindConTarget identifier target current = case target of
      State.NormalCon coreId -> State.aliasCon identifier coreId current
      State.ForeignCon _ -> current

applyParameters :: Span -> C.GlobalId -> [String] -> C.Con
applyParameters location identifier parameters =
  foldl' (\function index -> Located location (C.CApp function (Located location (C.CRel index))))
    (Located location (C.CNamed identifier))
    (reverse [0 .. length parameters - 1])

classifyDatatype :: [(String, identifier, Maybe typ)] -> E.DatatypeKind
classifyDatatype constructors
  | all noPayload constructors = E.Enum
  | length constructors == 2 && length (filter noPayload constructors) == 1 = E.Option
  | otherwise = E.Default
  where noPayload (_, _, payload) = case payload of Nothing -> True; Just _ -> False

isPageType :: State.CorifyState -> E.Con -> Bool
isPageType state = go Set.empty
  where
    go seen typ = case locatedValue typ of
      E.CNamed identifier -> case expandNamed seen identifier of
        Just (seen', definition) -> go seen' definition
        Nothing -> False
      E.TFun _ result -> go seen result
      E.CApp transaction payload -> isBasis seen "transaction" transaction && isHtmlXml seen payload
      _ -> False
    isBasis seen name constructor = case locatedValue constructor of
      E.CNamed identifier ->
        State.lookupForeignCon identifier state == Just ("Basis", name)
          || maybe False (\(seen', definition) -> isBasis seen' name definition) (expandNamed seen identifier)
      E.CModProj actual [] found -> Just actual == State.stateBasisId state && name == found
      _ -> False
    isHtmlXml seen constructor
      | isBasis seen "page" constructor = True
      | isBasis seen "xhtml" constructor = True
      | otherwise = case locatedValue constructor of
          E.CNamed identifier -> maybe False (uncurry isHtmlXml) (expandNamed seen identifier)
          E.CApp function _ -> isHtmlXml seen function || containsHtml seen constructor
          _ -> containsHtml seen constructor
    containsHtml seen constructor = case locatedValue constructor of
      E.CNamed identifier -> maybe False (uncurry containsHtml) (expandNamed seen identifier)
      E.CName "Html" -> True
      E.CApp left right -> containsHtml seen left || containsHtml seen right
      E.CRecord _ fields -> any (containsHtml seen . fst) fields || any (containsHtml seen . snd) fields
      _ -> False
    expandNamed seen identifier
      | Set.member identifier seen = Nothing
      | otherwise = (Set.insert identifier seen,) <$> State.lookupConDefinition identifier state

containsPostBody :: State.CorifyState -> E.Con -> Bool
containsPostBody state = go Set.empty
  where
    go seen constructor = case locatedValue constructor of
      E.CNamed identifier
        | State.lookupForeignCon identifier state == Just ("Basis", "postBody") -> True
        | Set.member identifier seen -> False
        | otherwise -> maybe False (go (Set.insert identifier seen)) (State.lookupConDefinition identifier state)
      E.CModProj actual [] "postBody" -> Just actual == State.stateBasisId state
      E.TFun left right -> go seen left || go seen right
      E.CApp left right -> go seen left || go seen right
      E.TRecord row -> go seen row
      E.CRecord _ fields -> any (go seen . fst) fields || any (go seen . snd) fields
      _ -> False

restName :: [RewriteRule] -> PathKind -> [String] -> String -> String
restName rewrites pathKind modules name =
  rewriteProjectPath rewrites pathKind (filter (/= '$') (intercalate "/" (reverse (stripWrap name : modules))))
  where stripWrap value = maybe value id (dropPrefix "wrap_" value)

sqlName :: [RewriteRule] -> PathKind -> [String] -> String -> String
sqlName rewrites pathKind modules = map sanitize . restName rewrites pathKind modules
  where sanitize '/' = '_'; sanitize character | isAlphaNum character || character == '_' = character; sanitize _ = '_'

dropPrefix :: Eq value => [value] -> [value] -> Maybe [value]
dropPrefix [] values = Just values
dropPrefix _ [] = Nothing
dropPrefix (expected : prefix) (actual : values)
  | expected == actual = dropPrefix prefix values
  | otherwise = Nothing

failure :: Located value -> String -> String -> Either Diagnostic result
failure source code message = Left (diagnostic CorePhase code (locatedSpan source) message)

foldlM :: Monad monad => (state -> value -> monad state) -> state -> [value] -> monad state
foldlM _ state [] = pure state
foldlM step state (value : rest) = step state value >>= \state' -> foldlM step state' rest

maximumGlobal :: E.File -> Int
maximumGlobal declarations = maximum (0 : concatMap declarationIds declarations)

declarationIds :: E.Decl -> [Int]
declarationIds declaration = case locatedValue declaration of
  E.DCon _ identifier _ _ -> one identifier
  E.DDatatype definitions -> concatMap datatypeIds definitions
  E.DDatatypeImp _ identifier original _ _ _ constructors -> one identifier <> one original <> concatMap constructorIds constructors
  E.DVal _ identifier _ _ -> one identifier
  E.DValRec bindings -> [E.unGlobalId identifier | (_, identifier, _, _) <- bindings]
  E.DSgn _ identifier _ -> one identifier
  E.DStr _ identifier _ structure -> one identifier <> structureIds structure
  E.DFfiStr _ identifier _ -> one identifier
  E.DExport identifier _ structure -> one identifier <> structureIds structure
  E.DTable basis _ identifier _ _ _ _ _ -> one basis <> one identifier
  E.DSequence basis _ identifier -> one basis <> one identifier
  E.DView basis _ identifier _ _ -> one basis <> one identifier
  E.DIndex {} -> []
  E.DDatabase {} -> []
  E.DCookie basis _ identifier _ -> one basis <> one identifier
  E.DStyle basis _ identifier -> one basis <> one identifier
  E.DTask {} -> []
  E.DPolicy {} -> []
  E.DOnError identifier _ _ -> one identifier
  E.DFfi _ identifier _ _ -> one identifier
  where one = pure . E.unGlobalId

datatypeIds :: (String, E.GlobalId, [String], [(String, E.GlobalId, Maybe E.Con)]) -> [Int]
datatypeIds (_, identifier, _, constructors) = E.unGlobalId identifier : concatMap constructorIds constructors

constructorIds :: (String, E.GlobalId, Maybe E.Con) -> [Int]
constructorIds (_, identifier, _) = [E.unGlobalId identifier]

structureIds :: E.Structure -> [Int]
structureIds structure = case locatedValue structure of
  E.StrConst declarations -> concatMap declarationIds declarations
  E.StrVar identifier -> [E.unGlobalId identifier]
  E.StrProj parent _ -> structureIds parent
  E.StrFun _ identifier _ _ body -> E.unGlobalId identifier : structureIds body
  E.StrApp function argument -> structureIds function <> structureIds argument
