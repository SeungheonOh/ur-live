{-# LANGUAGE LambdaCase #-}

-- | Complete surface-to-Elab traversal.  The specialized algorithms are kept
-- in the Elaborate directory; this module owns their sequencing and the
-- expression/declaration/module judgments.
module Vr.Elaborate
  ( elaborateFile
  , elaborateFileM
  , zonkFile
  , zonkSignature
  , elaborateSignature
  , inferExpression
  , inferStructure
  , solveAllConstraints
  , validateResolvedFile
  ) where

import Control.Monad (foldM, forM, forM_, unless, when)
import Control.Applicative ((<|>))
import Control.Monad.State.Strict (gets, modify')
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import qualified Data.Set as Set
import Vr.Elaborate.Classes
import Vr.Elaborate.Context
import Vr.Elaborate.Disjoint
import Vr.Elaborate.Expression
import Vr.Elaborate.Finalize
import Vr.Elaborate.Modules
import Vr.Elaborate.Patterns
import Vr.Elaborate.Solve
import Vr.Elaborate.State
import Vr.Elaborate.Types
import qualified Vr.Source as S
import Vr.Source (Explicitness (..), Located (..), Span)

elaborateFile :: Environment -> S.SFile -> (Either [S.Diagnostic] File, ElabState)
elaborateFile environment source = runElabM environment $ do
  file <- elaborateFileM source
  solveAllConstraints
  validateResolvedFile file
  zonkFile file

elaborateFileM :: S.SFile -> ElabM File
elaborateFileM declarations = do
  environment <- getEnvironment
  (declarations', finalEnvironment) <- elaborateDeclarations environment declarations
  putEnvironment finalEnvironment
  pure declarations'


elaborateSignature :: Environment -> S.SSignature -> ElabM (Signature, Environment)
elaborateSignature environment source = withEnvironment environment $ do
  case signatureWildcardSpan source of
    Just wildcardAt -> withSpanError "signature-wildcard" wildcardAt "Wildcard not allowed in signature"
    Nothing -> pure ()
  case locatedValue source of
    S.SSigConst items -> do
      (items', finalEnvironment) <- elaborateSignatureItems environment items
      pure (at (SgnConst items'), finalEnvironment)
    S.SSigVar name -> case Map.lookup name (environmentSignatures environment) of
      Just binding -> pure (at (SgnVar (signatureBindingId binding)), environment)
      Nothing -> do
        withSpanError "unbound-signature" location ("Unbound signature " <> name)
        pure (at SgnError, environment)
    S.SSigFun moduleName domain range -> do
      (domain', _) <- elaborateSignature environment domain
      identifier <- freshGlobal
      let environmentBase = insertStructureBinding moduleName (StructureBinding identifier (selfify identifier [] domain')) environment
      environment' <- openProjectedSignatureConstraints identifier [] domain' environmentBase domain'
      (range', _) <- elaborateSignature environment' range
      pure (at (SgnFun moduleName identifier domain' range'), environment)
    S.SSigWhere base path name definition -> do
      (base', _) <- elaborateSignature environment base
      definition' <- inferConIn environment definition >>= pure . fst
      pure (at (SgnWhere base' path name definition'), environment)
    S.SSigProj first modules name -> case Map.lookup first (environmentStructures environment) of
      Nothing -> do
        withSpanError "unbound-structure" location ("Unbound structure " <> first)
        pure (at SgnError, environment)
      Just binding -> pure (at (SgnProj (structureBindingId binding) modules name), environment)
  where
    location = S.locatedSpan source
    at = Located location

elaborateSignatureItems :: Environment -> [S.SSigItem] -> ElabM ([SigItem], Environment)
elaborateSignatureItems environment items = do
  baseline <- gets elaborationConstraints
  go baseline Set.empty [] environment items
  where
    go _ _ done current [] = pure (done, current)
    go baseline seen done current (item : rest) = do
      (items', environment') <- elaborateSignatureItem current item
      let introduced = concatMap (signatureItemNamespaces . locatedValue) items'
      forM_ introduced $ \entry@(namespace, name) ->
        when (Set.member entry seen) $
          withSpanError "duplicate-signature-item" (locatedSpan item) ("Duplicate " <> namespace <> " " <> name <> " in signature")
      let seen' = foldr Set.insert seen introduced
      -- This surprising reset is observable reference behavior: class
      -- signature items return a fresh goal list instead of preserving the
      -- fold accumulator.  Basis relies on it for four abstract row goals.
      when (isClassItem item) (modify' (\state -> state {elaborationConstraints = baseline}))
      go baseline seen' (done <> items') environment' rest
    isClassItem item = case locatedValue item of
      S.SSIClassAbs {} -> True
      S.SSIClass {} -> True
      _ -> False

signatureItemNamespaces :: SigItemF -> [(String, String)]
signatureItemNamespaces item = case item of
  SgiConAbs name _ _ -> [("constructor", name)]
  SgiCon name _ _ _ -> [("constructor", name)]
  SgiClassAbs name _ _ -> [("constructor", name)]
  SgiClass name _ _ _ -> [("constructor", name)]
  SgiDatatype definitions ->
    [("constructor", name) | (name, _, _, _) <- definitions]
      <> [("value", constructor) | (_, _, _, constructors) <- definitions, (constructor, _, _) <- constructors]
  SgiDatatypeImp name _ _ _ _ _ constructors ->
    ("constructor", name) : [("value", constructor) | (constructor, _, _) <- constructors]
  SgiVal name _ _ -> [("value", name)]
  SgiStr _ name _ _ -> [("structure", name)]
  SgiSgn name _ _ -> [("signature", name)]
  _ -> []

signatureWildcardSpan :: S.SSignature -> Maybe Span
signatureWildcardSpan signature = case locatedValue signature of
  S.SSigConst items -> firstMap signatureItemWildcardSpan items
  S.SSigFun _ domain range -> signatureWildcardSpan domain <|> signatureWildcardSpan range
  S.SSigWhere base _ _ definition -> signatureWildcardSpan base <|> conWildcardSpan definition
  _ -> Nothing

signatureItemWildcardSpan :: S.SSigItem -> Maybe Span
signatureItemWildcardSpan item = case locatedValue item of
  S.SSICon _ _ definition -> conWildcardSpan definition
  S.SSIDatatype definitions -> firstMap datatypeWildcard definitions
  S.SSIVal _ typ -> conWildcardSpan typ
  S.SSITable _ row _ _ -> conWildcardSpan row
  S.SSIStr _ signature -> signatureWildcardSpan signature
  S.SSISgn _ signature -> signatureWildcardSpan signature
  S.SSIInclude signature -> signatureWildcardSpan signature
  S.SSIConstraint left right -> conWildcardSpan left <|> conWildcardSpan right
  S.SSIClass _ _ definition -> conWildcardSpan definition
  _ -> Nothing
  where
    datatypeWildcard (_, _, constructors) = firstMap (maybe Nothing conWildcardSpan . third) constructors
    third (_, payload) = payload

conWildcardSpan :: S.SCon -> Maybe Span
conWildcardSpan constructor = case locatedValue constructor of
  S.SCWild {} -> Just (locatedSpan constructor)
  S.SCAnnot value _ -> conWildcardSpan value
  S.SCTFun domain range -> descend [domain, range]
  S.SCTCFun _ _ _ body -> conWildcardSpan body
  S.SCTRecord row -> conWildcardSpan row
  S.SCTDisjoint left right body -> descend [left, right, body]
  S.SCApp function argument -> descend [function, argument]
  S.SCAbs _ _ body -> conWildcardSpan body
  S.SCKAbs _ body -> conWildcardSpan body
  S.SCTKFun _ body -> conWildcardSpan body
  S.SCRecord fields -> firstMap (\(name, value) -> conWildcardSpan name <|> conWildcardSpan value) fields
  S.SCConcat left right -> descend [left, right]
  S.SCTuple elements -> descend elements
  S.SCProj tuple _ -> conWildcardSpan tuple
  _ -> Nothing
  where
    descend = firstMap conWildcardSpan

firstMap :: (value -> Maybe result) -> [value] -> Maybe result
firstMap _ [] = Nothing
firstMap function (value : rest) = function value <|> firstMap function rest

elaborateSignatureItem :: Environment -> S.SSigItem -> ElabM ([SigItem], Environment)
elaborateSignatureItem environment source = withEnvironment environment $ case locatedValue source of
  S.SSIConAbs name sourceKind -> do
    kind <- elaborateKind sourceKind
    identifier <- freshGlobal
    let environment' = insertConstructor name identifier kind Nothing False environment
    pure ([at (SgiConAbs name identifier kind)], environment')
  S.SSICon name maybeKind definition -> do
    (definition', inferredKind) <- inferCon definition
    kind <- maybe (pure inferredKind) elaborateKind maybeKind
    unifyKind location inferredKind kind
    identifier <- freshGlobal
    let environment' = insertConstructor name identifier kind (Just definition') False environment
    pure ([at (SgiCon name identifier kind definition')], environment')
  S.SSIDatatype definitions -> do
    (definitions', environment') <- elaborateDatatypes environment location definitions
    pure ([at (SgiDatatype definitions')], environment')
  S.SSIDatatypeImp name modules importedName -> do
    imported <- importDatatypeDefinition environment location name modules importedName
    case imported of
      Nothing -> pure ([], environment)
      Just (item, environment') -> pure ([at item], environment')
  S.SSIVal name sourceType -> do
    typ <- checkCon sourceType (at KType)
    identifier <- freshGlobal
    let expression = at (ENamed identifier)
        environment' = bindNamedValue name identifier typ expression environment
    pure ([at (SgiVal name identifier typ)], environment')
  S.SSITable name row primary constraints -> do
    row' <- checkCon row (at (KRecord (at KType)))
    let constraintKind = at (KRecord (at (KRecord (at KUnit))))
        hiddenName = name <> "_hidden_constraints"
    primaryKeys <- freshConMeta location 0 constraintKind "primary-key"
    visibleConstraints <- freshConMeta location 0 constraintKind "visible-constraints"
    hiddenIdentifier <- freshGlobal
    let hiddenConstraints = at (CNamed hiddenIdentifier)
        environmentWithHidden = insertConstructor hiddenName hiddenIdentifier constraintKind Nothing False environment
    (_, primaryType) <- inferExpression environmentWithHidden primary
    (_, constraintType) <- inferExpression environmentWithHidden constraints
    let expectedPrimary = basisApplied environmentWithHidden location "primary_key" [row', primaryKeys]
        expectedConstraints = basisApplied environmentWithHidden location "sql_constraints" [row', visibleConstraints]
    unifyCon environmentWithHidden primaryType expectedPrimary
    unifyCon environmentWithHidden constraintType expectedConstraints
    let knownConstraints = at (CConcat primaryKeys visibleConstraints)
        allConstraints = at (CConcat primaryKeys (at (CConcat visibleConstraints hiddenConstraints)))
    environmentWithConstraint <- assertDisjoint environmentWithHidden knownConstraints hiddenConstraints
    identifier <- freshGlobal
    let tableType = basisApplied environmentWithConstraint location "sql_table" [row', allConstraints]
        environment' = bindNamedValue name identifier tableType (at (ENamed identifier)) environmentWithConstraint
    pure
      ( [ at (SgiConAbs hiddenName hiddenIdentifier constraintKind)
        , at (SgiConstraint knownConstraints hiddenConstraints)
        , at (SgiVal name identifier tableType)
        ]
      , environment'
      )
  S.SSIStr name signatureSource -> do
    (signature, _) <- elaborateSignature environment signatureSource
    identifier <- freshGlobal
    let publicSignature = selfify identifier [] signature
        environmentBase = insertStructureBinding name (StructureBinding identifier publicSignature) environment
    environment' <- openProjectedSignatureConstraints identifier [] signature environmentBase signature
    pure ([at (SgiStr Import name identifier publicSignature)], environment')
  S.SSISgn name signatureSource -> do
    (signature, _) <- elaborateSignature environment signatureSource
    identifier <- freshGlobal
    let environment' = insertSignatureBinding name (SignatureBinding identifier signature) environment
    pure ([at (SgiSgn name identifier signature)], environment')
  S.SSIInclude signatureSource -> do
    (signature, _) <- elaborateSignature environment signatureSource
    case signatureItems environment signature of
      Just items -> pure (items, importSignature Import signature environment)
      Nothing -> withSpanError "signature-include" location "Only a constant signature can be included" >> pure ([], environment)
  S.SSIConstraint left right -> do
    (left', leftKind) <- inferCon left
    (right', rightKind) <- inferCon right
    leftElement <- freshKindMeta location "constraint-left"
    rightElement <- freshKindMeta location "constraint-right"
    unifyKind location leftKind (at (KRecord leftElement))
    unifyKind location rightKind (at (KRecord rightElement))
    environment' <- assertDisjoint environment left' right'
    pure ([at (SgiConstraint left' right')], environment')
  S.SSIClassAbs name sourceKind -> do
    kind <- elaborateKind sourceKind
    identifier <- freshGlobal
    let environment' = registerClass name identifier kind Nothing environment
    pure ([at (SgiClassAbs name identifier kind)], environment')
  S.SSIClass name sourceKind definition -> do
    kind <- elaborateKind sourceKind
    definition' <- checkCon definition kind
    identifier <- freshGlobal
    let environment' = registerClass name identifier kind (Just definition') environment
    pure ([at (SgiClass name identifier kind definition')], environment')
  where
    location = S.locatedSpan source
    at = Located location

elaborateDatatypes
  :: Environment
  -> Span
  -> [(String, [String], [(String, Maybe S.SCon)])]
  -> ElabM ([(String, GlobalId, [String], [(String, GlobalId, Maybe Con)])], Environment)
elaborateDatatypes environment at definitions = do
  allocated <- forM definitions $ \(name, parameters, constructors) -> do
    identifier <- freshGlobal
    pure (name, identifier, parameters, constructors)
  let withTypes = foldl (\current (name, identifier, parameters, _) -> insertConstructor name identifier (datatypeKind at parameters) Nothing False current) environment allocated
  foldM elaborateOne ([], withTypes) allocated
  where
    elaborateOne (done, current) (name, typeId, parameters, constructors) = do
      let parameterEnvironment = foldl (\currentEnvironment parameter -> pushRelativeCon parameter (Located at KType) currentEnvironment) current parameters
      constructors' <- forM constructors $ \(constructorName, argument) -> do
        identifier <- freshGlobal
        argument' <- traverse (\source -> withEnvironment parameterEnvironment (checkCon source (Located at KType))) argument
        pure (constructorName, identifier, argument')
      let datatypeClass = classify constructors'
          datatypeBinding = DatatypeBinding typeId parameters
            [(constructorName, dataBinding datatypeClass typeId parameters constructorName identifier argument) | (constructorName, identifier, argument) <- constructors']
          current' = foldl (insertDataConstructor datatypeClass typeId parameters) current constructors'
          current'' = current' {environmentDatatypes = Map.insert typeId datatypeBinding (environmentDatatypes current')}
      pure (done <> [(name, typeId, parameters, constructors')], current'')
    dataBinding datatypeClass typeId parameters _ identifier argument =
      DataConstructorBinding datatypeClass identifier typeId parameters argument (dataScheme at typeId parameters argument)
    insertDataConstructor datatypeClass typeId parameters current (name, identifier, argument) =
      let scheme = dataScheme at typeId parameters argument
          binding = DataConstructorBinding datatypeClass identifier typeId parameters argument scheme
       in (bindNamedValue name identifier scheme (Located at (ENamed identifier)) current)
            {environmentDataConstructors = Map.insert name binding (environmentDataConstructors current)}

importDatatypeDefinition :: Environment -> Span -> String -> [String] -> String -> ElabM (Maybe (SigItemF, Environment))
importDatatypeDefinition environment at name modules importedName = case resolveStructurePath environment modules of
  Nothing -> withSpanError "unbound-structure" at ("Unbound datatype path " <> qualify modules importedName) >> pure Nothing
  Just (root, path, signature) -> case projectDatatype signature importedName of
    Nothing -> withSpanError "unbound-datatype" at ("Unbound datatype " <> qualify modules importedName) >> pure Nothing
    Just datatype -> do
      identifier <- freshGlobal
      constructors <- forM (datatypeBindingConstructors datatype) $ \(constructorName, binding) -> do
        newIdentifier <- freshGlobal
        pure (constructorName, newIdentifier, dataConstructorArgument binding)
      let parameters = datatypeBindingParameters datatype
          item = SgiDatatypeImp name identifier root path importedName parameters constructors
          environment' = importSignature Import (Located at (SgnConst [Located at item])) environment
      pure (Just (item, environment'))

insertConstructor :: String -> GlobalId -> Kind -> Maybe Con -> Bool -> Environment -> Environment
insertConstructor name identifier kind definition isClass environment =
  insertConBinding name (ConBinding identifier kind definition isClass) environment

datatypeKind :: Span -> [String] -> Kind
datatypeKind at parameters = foldr (const (\result -> Located at (KArrow (Located at KType) result))) (Located at KType) parameters

dataScheme :: Span -> GlobalId -> [String] -> Maybe Con -> Con
dataScheme at typeId parameters argument = foldr quantify body parameters
  where
    result = foldl (\function index -> Located at (CApp function (Located at (CRel index)))) (Located at (CNamed typeId)) [length parameters - 1, length parameters - 2 .. 0]
    body = maybe result (\domain -> Located at (TFun domain result)) argument
    quantify name rest = Located at (TCFun Implicit name (Located at KType) rest)

classify :: [(String, GlobalId, Maybe Con)] -> DatatypeKind
classify constructors = case map (maybe False (const True) . third) constructors of
  [False, True] -> Option
  [True, False] -> Option
  arguments | not (or arguments) -> Enum
  _ -> Default
  where third (_, _, value) = value

elaborateDeclarations :: Environment -> [S.SDecl] -> ElabM ([Decl], Environment)
elaborateDeclarations = go []
  where
    go done environment [] = pure (done, environment)
    go done environment (source : rest) = do
      (declarations, environment') <- elaborateDeclaration environment source
      settleDelayedRows
      go (done <> declarations) environment' rest

elaborateDeclaration :: Environment -> S.SDecl -> ElabM ([Decl], Environment)
elaborateDeclaration environment source = withEnvironment environment $ case locatedValue source of
  S.SDCon name annotation definition -> do
    (definition', inferredKind) <- inferCon definition
    kind <- maybe (pure inferredKind) elaborateKind annotation
    unifyKind location inferredKind kind
    identifier <- freshGlobal
    let environment' = insertConstructor name identifier kind (Just definition') False environment
    pure ([at (DCon name identifier kind definition')], environment')
  S.SDDatatype definitions -> do
    (definitions', environment') <- elaborateDatatypes environment location definitions
    pure ([at (DDatatype definitions')], environment')
  S.SDDatatypeImp name modules importedName -> do
    imported <- importDatatypeDefinition environment location name modules importedName
    case imported of
      Nothing -> pure ([], environment)
      Just (SgiDatatypeImp itemName identifier original path originalName parameters constructors, environment') ->
        pure ([at (DDatatypeImp itemName identifier original path originalName parameters constructors)], environment')
      Just _ -> pure ([], environment)
  S.SDVal patternSource expression -> elaborateTopValue environment location patternSource expression
  S.SDValRec bindings -> do
    prepared <- forM bindings $ \(name, annotation, expression) -> do
      identifier <- freshGlobal
      typ <- maybe (freshConMeta location 0 (at KType) name) (\sourceType -> checkCon sourceType (at KType)) annotation
      pure (name, identifier, typ, expression)
    let recursiveEnvironment = foldl (\current (name, identifier, typ, _) -> bindNamedValue name identifier typ (at (ENamed identifier)) current) environment prepared
    bindings' <- forM prepared $ \(name, identifier, typ, expression) -> do
      (expression', actualType) <- inferExpression recursiveEnvironment expression
      unifyCon recursiveEnvironment actualType typ
      unless (allowableRecursive expression) (withSpanError "illegal-recursion" (S.locatedSpan expression) ("Recursive value " <> name <> " is not a function"))
      pure (name, identifier, typ, expression')
    -- Keep a top-level recursive binding named after checking it.  Ur/Web's
    -- Core pipeline decides later whether a non-recursive SCC should be
    -- inlined or monomorphized; substituting the checked body here bypasses
    -- CoreUntangle, Reduce, and Unpoly and duplicates polymorphic lambdas at
    -- every source use.
    let finalEnvironment = foldl (\current (name, identifier, typ, _) -> bindNamedValue name identifier typ (at (ENamed identifier)) current) recursiveEnvironment bindings'
    pure ([at (DValRec bindings')], finalEnvironment)
  S.SDSgn name signatureSource -> do
    (signature, _) <- elaborateSignature environment signatureSource
    identifier <- freshGlobal
    let environment' = insertSignatureBinding name (SignatureBinding identifier signature) environment
    pure ([at (DSgn name identifier signature)], environment')
  S.SDStr name annotation _ structureSource _ -> do
    -- The pinned Ur/Web elaborator loses the old structure identity when an
    -- annotated structure alias shadows that same name.  It ultimately
    -- rejects the declaration with its internal UnboundNamed exception.
    -- Preserve the observable frontend result without reproducing the crash.
    case (annotation, Map.lookup name (environmentStructures environment), locatedValue structureSource) of
      (Just _, Just previous, S.SStrVar target) ->
        case Map.lookup target (environmentStructures environment) of
          Just current
            | structureBindingId previous /= structureBindingId current ->
                withSpanError "shadowed-structure-alias" location "Annotated structure alias shadows a different structure"
          _ -> pure ()
      _ -> pure ()
    expected <- traverse (fmap fst . elaborateSignature environment) annotation
    completedSource <- maybe (pure structureSource) (\signature -> wildifyStructure environment signature structureSource) expected
    (structure, actualSignature) <- inferStructure environment completedSource
    signature <- case expected of
      Nothing -> pure actualSignature
      Just expectedSignature -> do
        subsignature environment location actualSignature expectedSignature
        pure expectedSignature
    identifier <- freshGlobal
    let publicSignature = case (annotation, locatedValue structure) of
          (Nothing, StrVar {}) -> signature
          (Nothing, StrProj {}) -> signature
          _ -> selfify identifier [] signature
        environmentBase = insertStructureBinding name (StructureBinding identifier publicSignature) environment
    environment' <- openProjectedSignatureConstraints identifier [] signature environmentBase signature
    pure ([at (DStr name identifier publicSignature structure)], environment')
  S.SDFfiStr name signatureSource _ -> do
    (signature, _) <- elaborateSignature environment signatureSource
    case locatedValue signature of
      SgnConst items -> case listToMaybe (filter (not . ffiSignatureItemAllowed . locatedValue) items) of
        Nothing -> pure ()
        Just _ -> withSpanError "ffi-signature-item" location "Disallowed signature item for FFI module"
      _ -> withSpanError "ffi-signature-form" location "FFI signature is not a constant signature"
    identifier <- freshGlobal
    let publicSignature = selfify identifier [] signature
        environmentBase = insertStructureBinding name (StructureBinding identifier publicSignature) environment
    environment' <- openProjectedSignatureConstraints identifier [] signature environmentBase signature
    pure ([at (DFfiStr name identifier publicSignature)], environment')
  S.SDOpen first path -> case resolveStructurePath environment (first : path) of
    Nothing -> withSpanError "unbound-structure" location ("Cannot open structure " <> qualify (first : path) "") >> pure ([], environment)
    Just (root, projectedPath, signature) -> do
      let (opened, environmentBase) = openSignatureDeclarations root projectedPath signature environment
      environment' <- openProjectedSignatureConstraints root projectedPath signature environmentBase signature
      pure (opened, environment')
  S.SDConstraint left right -> do
    (left', leftKind) <- inferCon left
    (right', rightKind) <- inferCon right
    leftElement <- freshKindMeta location "constraint-left"
    rightElement <- freshKindMeta location "constraint-right"
    unifyKind location leftKind (at (KRecord leftElement))
    unifyKind location rightKind (at (KRecord rightElement))
    environment' <- assertDisjoint environment left' right'
    pure ([at (DConstraint left' right')], environment')
  S.SDOpenConstraints first path -> case resolveStructurePath environment (first : path) of
    Nothing -> withSpanError "unbound-structure" location ("Cannot open constraints from " <> qualify (first : path) "") >> pure ([], environment)
    Just (root, projectedPath, signature) -> (,) [] <$> openProjectedSignatureConstraints root projectedPath signature environment signature
  S.SDExport structureSource -> do
    (structure, signature) <- inferStructure environment structureSource
    identifier <- freshGlobal
    pure ([at (DExport identifier signature structure)], environment)
  S.SDTable name row primary constraints -> do
    row' <- checkCon row (at (KRecord (at KType)))
    pkey <- freshConMeta location 0 (at (KRecord (at (KRecord (at KUnit))))) "primary-key"
    uniques <- freshConMeta location 0 (at (KRecord (at (KRecord (at KUnit))))) "constraints"
    basisIdentifier <- basisStructureIdentifier environment location
    identifier <- freshGlobal
    let tableType = basisApplied environment location "sql_table" [row', at (CConcat pkey uniques)]
        environmentWithTable = bindNamedValue name identifier tableType (at (ENamed identifier)) environment
    (primary', primaryType) <- inferExpression environmentWithTable primary
    (constraints', constraintType) <- inferExpression environmentWithTable constraints
    let expectedPrimary = basisApplied environmentWithTable location "primary_key" [row', pkey]
        expectedConstraints = basisApplied environmentWithTable location "sql_constraints" [row', uniques]
    unifyCon environmentWithTable primaryType expectedPrimary
    unifyCon environmentWithTable constraintType expectedConstraints
    let environment' = environmentWithTable
    pure ([at (DTable basisIdentifier name identifier row' primary' pkey constraints' uniques)], environment')
  S.SDSequence name -> do
    basisIdentifier <- basisStructureIdentifier environment location
    identifier <- freshGlobal
    let typ = basisApplied environment location "sql_sequence" []
        environment' = bindNamedValue name identifier typ (at (ENamed identifier)) environment
    pure ([at (DSequence basisIdentifier name identifier)], environment')
  S.SDView name expression -> do
    (expression', expressionType) <- inferExpression environment expression
    row <- freshConMeta location 0 (at (KRecord (at KType))) "view-row"
    let fieldRowKind = at (KRecord (at KType))
        tableRowKind = at (KRecord fieldRowKind)
    selectedTables <- freshConMeta location 0 tableRowKind "view-selected-tables"
    let emptyOuter = at (CRecord fieldRowKind [])
        emptyFields = at (CRecord (at KType) [])
        eraseFields = at (CAbs "_" fieldRowKind emptyFields)
        mapRows = at (CMap fieldRowKind fieldRowKind)
        emptySelectedTables = at (CApp (at (CApp mapRows eraseFields)) selectedTables)
        expectedQuery = basisApplied environment location "sql_query"
          [emptyOuter, emptyOuter, emptySelectedTables, row]
    unifyCon environment expressionType expectedQuery
    basisIdentifier <- basisStructureIdentifier environment location
    identifier <- freshGlobal
    let typ = basisApplied environment location "sql_view" [row]
        environment' = bindNamedValue name identifier typ (at (ENamed identifier)) environment
    pure ([at (DView basisIdentifier name identifier expression' row)], environment')
  S.SDIndex table modes fields -> do
    (table', tableType) <- inferExpression environment table
    (modes', modesType) <- inferExpression environment modes
    used <- case fields of
      Nothing -> freshConMeta location 0 (at (KRecord (at KType))) "index-fields"
      Just sourceFields -> checkCon sourceFields (at (KRecord (at KType)))
    unused <- freshConMeta location 0 (at (KRecord (at KType))) "index-unused-fields"
    keys <- freshConMeta location 0 (at (KRecord (at (KRecord (at KUnit))))) "index-keys"
    let expectedTable = basisApplied environment location "sql_table" [at (CConcat used unused), keys]
        indexMode = basisApplied environment location "index_mode" []
        mapper = at (CMap (at KType) (at KType))
        modeRow = at (CApp (at (CApp mapper indexMode)) used)
        expectedModes = at (TRecord modeRow)
    unifyCon environment tableType expectedTable
    unifyCon environment modesType expectedModes
    pure ([at (DIndex table' modes')], environment)
  S.SDDatabase name -> pure ([at (DDatabase name)], environment)
  S.SDCookie name sourceType -> do
    payload <- checkCon sourceType (at KType)
    basisIdentifier <- basisStructureIdentifier environment location
    identifier <- freshGlobal
    let typ = basisApplied environment location "http_cookie" [payload]
        environment' = bindNamedValue name identifier typ (at (ENamed identifier)) environment
    pure ([at (DCookie basisIdentifier name identifier payload)], environment')
  S.SDStyle name -> do
    basisIdentifier <- basisStructureIdentifier environment location
    identifier <- freshGlobal
    let typ = basisApplied environment location "css_class" []
        environment' = bindNamedValue name identifier typ (at (ENamed identifier)) environment
    pure ([at (DStyle basisIdentifier name identifier)], environment')
  S.SDTask kind expression -> do
    (kind', kindType) <- inferExpression environment kind
    (expression', expressionType) <- inferExpression environment expression
    argument <- freshConMeta location 0 (at KType) "task-argument"
    let expectedKind = basisApplied environment location "task_kind" [argument]
        transactionUnit = basisApplied environment location "transaction" [at (TRecord (at (CRecord (at KType) [])))]
    unifyCon environment kindType expectedKind
    unifyCon environment expressionType (at (TFun argument transactionUnit))
    pure ([at (DTask kind' expression')], environment)
  S.SDPolicy expression -> do
    (expression', expressionType) <- inferExpression environment expression
    unifyCon environment expressionType (basisApplied environment location "sql_policy" [])
    pure ([at (DPolicy expression')], environment)
  S.SDOnError first path name -> case resolveStructurePath environment (first : path) of
    Nothing -> withSpanError "unbound-onerror" location ("Unbound onError function " <> qualify (first : path) name) >> pure ([at (DOnError (GlobalId (-1)) path name)], environment)
    Just (identifier, resolvedPath, signature) -> case projectValue signature name of
      Nothing -> withSpanError "unbound-onerror" location ("Unbound onError function " <> name) >> pure ([at (DOnError identifier resolvedPath name)], environment)
      Just binding -> do
        let actual = projectConAt identifier resolvedPath signature (valueBindingType binding)
            xbody = basisApplied environment location "xbody" []
            page = basisApplied environment location "page" []
            transaction = basisApplied environment location "transaction" [page]
        unifyCon environment actual (at (TFun xbody transaction))
        pure ([at (DOnError identifier resolvedPath name)], environment)
  S.SDFfi name modes sourceType -> do
    unless (environmentLessSafeFfi environment) $
      withSpanError "less-safe-ffi" location "To enable 'ffi' declarations, the .urp directive 'lessSafeFfi' is mandatory"
    typ <- checkCon sourceType (at KType)
    identifier <- freshGlobal
    let environment' = bindNamedValue name identifier typ (at (ENamed identifier)) environment
    pure ([at (DFfi name identifier modes typ)], environment')
  where
    location = S.locatedSpan source
    at = Located location

ffiSignatureItemAllowed :: SigItemF -> Bool
ffiSignatureItemAllowed item = case item of
  SgiConAbs {} -> True
  SgiCon {} -> True
  SgiDatatype {} -> True
  SgiVal {} -> True
  _ -> False

elaborateTopValue :: Environment -> Span -> S.SPattern -> S.SExpr -> ElabM ([Decl], Environment)
elaborateTopValue environment at patternSource expression = do
  (expression', expressionType) <- inferExpression environment expression
  (pattern', patternEnvironment) <- checkPattern environment patternSource expressionType
  checkPatternExhaustiveness environment (S.locatedSpan patternSource) expressionType [pattern']
  case locatedValue pattern' of
    PVar name typ | name /= "_" -> do
      identifier <- freshGlobal
      let environment' = bindNamedValue name identifier typ expression' environment
      pure ([Located at (DVal name identifier typ expression')], environment')
    _ -> do
      temporary <- freshGlobal
      let temporaryName = "?pattern" <> show (unGlobalId temporary)
          temporaryDecl = Located at (DVal temporaryName temporary expressionType expression')
          bindings = patternBindings pattern'
      extracted <- forM bindings $ \(name, typ, index) -> do
        identifier <- freshGlobal
        let scrutinee = Located at (ENamed temporary)
            branchValue = Located at (ERel index)
            value = Located at (ECase scrutinee [(pattern', branchValue)] expressionType typ)
        pure (Located at (DVal name identifier typ value), (name, identifier, typ, value))
      let environment' = foldl (\current (_, (name, identifier, typ, value)) -> bindNamedValue name identifier typ value current) environment extracted
      pure (temporaryDecl : map fst extracted, environment') <* pure patternEnvironment

basisStructureIdentifier :: Environment -> Span -> ElabM GlobalId
basisStructureIdentifier environment at = case Map.lookup "Basis" (environmentStructures environment) of
  Just binding -> pure (structureBindingId binding)
  Nothing -> do
    withSpanError "missing-basis" at "The Basis structure is not in scope"
    pure (GlobalId (-1))

patternBindings :: Pattern -> [(String, Con, Int)]
patternBindings pattern' = zipWith attach collected [length collected - 1, length collected - 2 .. 0]
  where
    collected = collect pattern'
    attach (name, typ) index = (name, typ, index)
    collect current = case locatedValue current of
      PVar name typ | name /= "_" -> [(name, typ)]
      PCon _ _ _ nested -> maybe [] collect nested
      PRecord fields _ -> concatMap (collect . fieldPattern) fields
      _ -> []
    fieldPattern (_, value, _) = value

inferStructure :: Environment -> S.SStructure -> ElabM (Structure, Signature)
inferStructure environment source = withEnvironment environment $ case locatedValue source of
  S.SStrConst declarations -> do
    (declarations', _) <- elaborateDeclarations environment declarations
    let items = deduplicateSignatureItems (concatMap declarationSignature declarations')
    pure (at (StrConst declarations'), at (SgnConst items))
  S.SStrVar name -> case Map.lookup name (environmentStructures environment) of
    Nothing -> withSpanError "unbound-structure" location ("Unbound structure " <> name) >> pure (at StrError, at SgnError)
    Just binding ->
      let identifier = structureBindingId binding
          signature = headNormalizeSignature environment (structureBindingSignature binding)
       in pure (at (StrVar identifier), projectSignatureAt identifier [] signature signature)
  S.SStrProj structureSource name -> do
    (structure, signature) <- inferStructure environment structureSource
    let enclosing = headNormalizeSignature environment signature
    case projectStructure enclosing name of
      Nothing -> withSpanError "unbound-structure-field" location ("Structure has no field " <> name) >> pure (at StrError, at SgnError)
      Just (_, nested) ->
        let projected = case structurePath structure of
              Just (root, path) -> projectSignatureAt root path enclosing nested
              Nothing -> nested
         in pure (at (StrProj structure name), projected)
  S.SStrFun name domainSource rangeSource bodySource -> do
    (domain, _) <- elaborateSignature environment domainSource
    identifier <- freshGlobal
    let bodyEnvironmentBase = insertStructureBinding name (StructureBinding identifier (selfify identifier [] domain)) environment
    bodyEnvironment <- openProjectedSignatureConstraints identifier [] domain bodyEnvironmentBase domain
    (body, actualRange) <- inferStructure bodyEnvironment bodySource
    range <- case rangeSource of
      Nothing -> pure actualRange
      Just expectedSource -> do
        (expected, _) <- elaborateSignature bodyEnvironment expectedSource
        subsignature bodyEnvironment location actualRange expected
        pure expected
    pure (at (StrFun name identifier domain range body), at (SgnFun name identifier domain range))
  S.SStrApp functionSource argumentSource -> do
    (function, functionSignature0) <- inferStructure environment functionSource
    let functionSignature = headNormalizeSignature environment functionSignature0
    argumentSource' <- case locatedValue functionSignature of
      SgnFun _ _ domain _ -> wildifyStructure environment domain argumentSource
      _ -> pure argumentSource
    (argument, argumentSignature) <- inferStructure environment argumentSource'
    case locatedValue functionSignature of
      SgnFun name identifier domain range -> do
        subsignature environment location argumentSignature domain
        -- A functor result keeps the formal module identity in its range.
        -- Ur makes that identity reducible by prepending a hidden structure
        -- item whose signature is the actual argument, selfified only when
        -- the argument itself is a projectable structure path.  Rewriting
        -- the formal projections directly loses the argument signature for
        -- literal structures and breaks generativity/manifest equations.
        let normalizedRange = headNormalizeSignature environment range
            argumentPublic = case structurePath argument of
              -- Our projected-constructor environment stores signatures
              -- directly rather than carrying the reference compiler's
              -- structure-expression substitution alongside them.  Expose
              -- the head here before selfification so an alias through a
              -- named signature still records equations such as M.t = SS.t.
              Just (root, path) -> selfify root path (headNormalizeSignature environment argumentSignature)
              Nothing -> argumentSignature
            hiddenName = unusedStructureName name normalizedRange
            item = Located location (SgiStr Skip hiddenName identifier argumentPublic)
            result' = case locatedValue normalizedRange of
              SgnConst items -> normalizedRange {locatedValue = SgnConst (item : items)}
              _ -> normalizedRange
        pure (at (StrApp function argument), result')
      _ -> withSpanError "not-functor" location "Structure application requires a functor" >> pure (at StrError, at SgnError)
  where
    location = S.locatedSpan source
    at = Located location
    structurePath structure = case locatedValue structure of
      StrVar identifier -> Just (identifier, [])
      StrProj parent name -> do
        (identifier, path) <- structurePath parent
        pure (identifier, path <> [name])
      _ -> Nothing
    unusedStructureName candidate signature = case locatedValue signature of
      SgnConst items
        | any (hasStructureName candidate) items -> unusedStructureName ('?' : candidate) signature
      _ -> candidate
    hasStructureName candidate item = case locatedValue item of
      SgiStr _ name _ _ -> name == candidate
      _ -> False

-- Ur completes literal functor arguments with inferable domain components.
-- This is observable surface behavior, not merely signature matching: missing
-- constructors become wild constructor declarations, constraints become
-- declarations, and class/folder values become wildcard values.
wildifyStructure :: Environment -> Signature -> S.SStructure -> ElabM S.SStructure
wildifyStructure environment formal source = case (locatedValue source, signatureItems environment formal) of
  (S.SStrConst declarations0, Just items) -> do
    declarations <- mapM (completeNested items) declarations0
    let at = S.locatedSpan source
        presentConstructors = Set.fromList (concatMap declaredConstructors declarations)
        presentValues = Set.fromList (concatMap declaredValues declarations)
        localNames = Map.fromList (concatMap constructorNames items)
    constructorDeclarations <- fmap concat $ forM items $ \item -> case locatedValue item of
      SgiConAbs name _ kind | Set.notMember name presentConstructors -> do
        sourceKind <- decompileKind at kind
        pure [Located at (S.SDCon name Nothing (Located at (S.SCWild sourceKind)))]
      SgiCon name _ kind _ | Set.notMember name presentConstructors -> do
        sourceKind <- decompileKind at kind
        pure [Located at (S.SDCon name Nothing (Located at (S.SCWild sourceKind)))]
      _ -> pure []
    constraintDeclarations <- fmap concat $ forM items $ \item -> case locatedValue item of
      SgiConstraint left right -> do
        left' <- decompileCon at localNames left
        right' <- decompileCon at localNames right
        pure (case (left', right') of
          (Just leftSource, Just rightSource) -> [Located at (S.SDConstraint leftSource rightSource)]
          _ -> [])
      _ -> pure []
    valueDeclarations <- fmap concat $ forM items $ \item -> case locatedValue item of
      SgiVal name _ typ | Set.notMember name presentValues -> do
        needed <- inferableDomainValue typ
        pure (if needed
          then [Located at (S.SDVal (Located at (S.SPVar name)) (Located at S.SEWild))]
          else [])
      _ -> pure []
    let (reversedSuffix, reversedPrefix) = break isConstructorLike (reverse declarations)
        prefix = reverse reversedPrefix
        suffix = reverse reversedSuffix
        generated = constructorDeclarations <> valueDeclarations <> constraintDeclarations
    pure source {locatedValue = S.SStrConst (prefix <> generated <> suffix)}
  _ -> pure source
  where
    completeNested items declaration = case locatedValue declaration of
      S.SDStr name annotation timestamp nested flag -> case nestedFormal items name of
        Nothing -> pure declaration
        Just signature -> do
          nested' <- wildifyStructure environment signature nested
          pure declaration {locatedValue = S.SDStr name annotation timestamp nested' flag}
      _ -> pure declaration
    nestedFormal items name = listToMaybe
      [signature | item <- items, SgiStr _ itemName _ signature <- [locatedValue item], itemName == name]
    declaredConstructors declaration = case locatedValue declaration of
      S.SDCon name _ _ -> [name]
      S.SDDatatype definitions -> [name | (name, _, _) <- definitions]
      S.SDDatatypeImp name _ _ -> [name]
      _ -> []
    declaredValues declaration = case locatedValue declaration of
      S.SDVal pattern' _ -> case locatedValue pattern' of
        S.SPVar name -> [name]
        _ -> []
      S.SDValRec bindings -> [name | (name, _, _) <- bindings]
      S.SDTable name _ _ _ -> [name]
      S.SDSequence name -> [name]
      S.SDView name _ -> [name]
      S.SDCookie name _ -> [name]
      S.SDStyle name -> [name]
      S.SDFfi name _ _ -> [name]
      _ -> []
    isConstructorLike declaration = case locatedValue declaration of
      S.SDCon {} -> True
      S.SDDatatype {} -> True
      S.SDDatatypeImp {} -> True
      S.SDStr {} -> True
      S.SDConstraint {} -> True
      _ -> False
    constructorNames item = case locatedValue item of
      SgiConAbs name identifier _ -> [(identifier, name)]
      SgiCon name identifier _ _ -> [(identifier, name)]
      SgiClassAbs name identifier _ -> [(identifier, name)]
      SgiClass name identifier _ _ -> [(identifier, name)]
      SgiDatatype definitions -> [(identifier, name) | (name, identifier, _, _) <- definitions]
      SgiDatatypeImp name identifier _ _ _ _ _ -> [(identifier, name)]
      _ -> []
    inferableDomainValue typ = do
      normalized <- headNormalizeCon environment typ
      pure (isClassLike environment normalized)

    decompileKind at kind0 = do
      kind <- zonkKind kind0
      pure (Located at (case locatedValue kind of
        KType -> S.SKType
        KArrow domain range -> S.SKArrow (kindSource domain) (kindSource range)
        KName -> S.SKName
        KRecord element -> S.SKRecord (kindSource element)
        KUnit -> S.SKUnit
        KTuple elements -> S.SKTuple (map kindSource elements)
        KFun name body -> S.SKFun name (kindSource body)
        _ -> S.SKWild))
      where
        kindSource kind = Located at (case locatedValue kind of
          KType -> S.SKType
          KArrow domain range -> S.SKArrow (kindSource domain) (kindSource range)
          KName -> S.SKName
          KRecord element -> S.SKRecord (kindSource element)
          KUnit -> S.SKUnit
          KTuple elements -> S.SKTuple (map kindSource elements)
          KFun name body -> S.SKFun name (kindSource body)
          _ -> S.SKWild)

    decompileCon at localNames constructor0 = do
      constructor <- zonkCon constructor0
      pure (go constructor)
      where
        go constructor = Located at <$> case locatedValue constructor of
          TFun domain range -> S.SCTFun <$> go domain <*> go range
          TCFun explicitness name kind body -> S.SCTCFun explicitness name (kindSource kind) <$> go body
          TRecord row -> S.SCTRecord <$> go row
          TDisjoint left right body -> S.SCTDisjoint <$> go left <*> go right <*> go body
          CRel index -> S.SCVar [] . relativeConName <$> indexMaybe index (environmentRelativeConstructors environment)
          CNamed identifier -> S.SCVar [] <$> (Map.lookup identifier localNames <|> globalConstructorName identifier)
          CModProj identifier path name -> do
            rootName <- structureName identifier
            pure (S.SCVar (rootName : path) name)
          CApp function argument -> S.SCApp <$> go function <*> go argument
          CAbs name kind body -> S.SCAbs name (Just (kindSource kind)) <$> go body
          CKAbs name body -> S.SCKAbs name <$> go body
          CKApp function _ -> locatedValue <$> go function
          TKFun name body -> S.SCTKFun name <$> go body
          CName name -> Just (S.SCName name)
          CRecord kind fields -> do
            fields' <- mapM (\(name, value) -> (,) <$> go name <*> go value) fields
            let record = Located at (S.SCRecord fields')
            pure (S.SCAnnot record (Located at (S.SKRecord (kindSource kind))))
          CConcat left right -> S.SCConcat <$> go left <*> go right
          CMap {} -> Just S.SCMap
          CUnit -> Just S.SCUnit
          CTuple elements -> S.SCTuple <$> mapM go elements
          CProj tuple index -> S.SCProj <$> go tuple <*> pure index
          CMeta _ _ kind _ -> Just (S.SCWild (kindSource kind))
          CError -> Nothing
        kindSource kind = Located at (case locatedValue kind of
          KType -> S.SKType
          KArrow domain range -> S.SKArrow (kindSource domain) (kindSource range)
          KName -> S.SKName
          KRecord element -> S.SKRecord (kindSource element)
          KUnit -> S.SKUnit
          KTuple elements -> S.SKTuple (map kindSource elements)
          KFun name body -> S.SKFun name (kindSource body)
          _ -> S.SKWild)
        globalConstructorName identifier =
          fst <$> Map.foldrWithKey (\name binding found -> found <|> if conBindingId binding == identifier then Just (name, binding) else Nothing) Nothing (environmentConstructors environment)
        structureName identifier =
          fst <$> Map.foldrWithKey (\name binding found -> found <|> if structureBindingId binding == identifier then Just (name, binding) else Nothing) Nothing (environmentStructures environment)
        indexMaybe index values | index >= 0 && index < length values = Just (values !! index)
        indexMaybe _ _ = Nothing

declarationSignature :: Decl -> [SigItem]
declarationSignature declaration = [Located at item | item <- case locatedValue declaration of
  DCon name identifier kind definition -> [SgiCon name identifier kind definition]
  DDatatype definitions -> [SgiDatatype definitions]
  DDatatypeImp name identifier original path originalName parameters constructors -> [SgiDatatypeImp name identifier original path originalName parameters constructors]
  DVal name identifier typ _ -> [SgiVal name identifier typ]
  DValRec bindings -> [SgiVal name identifier typ | (name, identifier, typ, _) <- bindings]
  DSgn name identifier signature -> [SgiSgn name identifier signature]
  DStr name identifier signature _ -> [SgiStr Import name identifier signature]
  DFfiStr name identifier signature -> [SgiStr Import name identifier signature]
  DConstraint left right -> [SgiConstraint left right]
  DTable basis name identifier row _ primary _ constraints ->
    [SgiVal name identifier (apply (apply (basisType basis "sql_table") row) (Located at (CConcat primary constraints)))]
  DSequence basis name identifier -> [SgiVal name identifier (basisType basis "sql_sequence")]
  DView basis name identifier _ row -> [SgiVal name identifier (apply (basisType basis "sql_view") row)]
  DCookie basis name identifier payload -> [SgiVal name identifier (apply (basisType basis "http_cookie") payload)]
  DStyle basis name identifier -> [SgiVal name identifier (basisType basis "css_class")]
  DFfi name identifier _ typ -> [SgiVal name identifier typ]
  _ -> []]
  where
    at = locatedSpan declaration
    basisType identifier name = Located at (CModProj identifier [] name)
    apply function argument = Located at (CApp function argument)

-- Inferred structure signatures retain the rightmost declaration under its
-- source name.  Earlier declarations in the same namespace are kept for the
-- typed program but hidden by a question-mark prefix.  This matters for the
-- idiom where a helper named @main@ is followed by the exported @main@.
deduplicateSignatureItems :: [SigItem] -> [SigItem]
deduplicateSignatureItems items = result
  where
    (result, _, _, _, _) = foldr step ([], Set.empty, Set.empty, Set.empty, Set.empty) items
    step item (done, constructors, values, signatures, structures) =
      case locatedValue item of
        SgiConAbs name identifier kind ->
          let (constructors', name') = claim constructors name
           in (item {locatedValue = SgiConAbs name' identifier kind} : done, constructors', values, signatures, structures)
        SgiCon name identifier kind definition ->
          let (constructors', name') = claim constructors name
           in (item {locatedValue = SgiCon name' identifier kind definition} : done, constructors', values, signatures, structures)
        SgiClassAbs name identifier kind ->
          let (constructors', name') = claim constructors name
           in (item {locatedValue = SgiClassAbs name' identifier kind} : done, constructors', values, signatures, structures)
        SgiClass name identifier kind definition ->
          let (constructors', name') = claim constructors name
           in (item {locatedValue = SgiClass name' identifier kind definition} : done, constructors', values, signatures, structures)
        SgiDatatype definitions ->
          let (definitions', constructors', values') = foldl renameDatatype ([], constructors, values) definitions
           in (item {locatedValue = SgiDatatype definitions'} : done, constructors', values', signatures, structures)
        SgiDatatypeImp name identifier original path originalName parameters dataConstructors ->
          let (constructors', name') = claim constructors name
           in (item {locatedValue = SgiDatatypeImp name' identifier original path originalName parameters dataConstructors} : done, constructors', values, signatures, structures)
        SgiVal name identifier typ ->
          let (values', name') = claim values name
           in (item {locatedValue = SgiVal name' identifier typ} : done, constructors, values', signatures, structures)
        SgiSgn name identifier signature ->
          let (signatures', name') = claim signatures name
           in (item {locatedValue = SgiSgn name' identifier signature} : done, constructors, values, signatures', structures)
        SgiStr mode name identifier signature ->
          let (structures', name') = claim structures name
           in (item {locatedValue = SgiStr mode name' identifier signature} : done, constructors, values, signatures, structures')
        SgiConstraint {} -> (item : done, constructors, values, signatures, structures)
    claim occupied name
      | Set.member name occupied = (occupied, '?' : name)
      | otherwise = (Set.insert name occupied, name)
    renameDatatype (done, constructors, values) (name, identifier, parameters, dataConstructors) =
      let (constructors', name') = claim constructors name
          (dataConstructors', values') = foldl renameDataConstructor ([], values) dataConstructors
       in (done <> [(name', identifier, parameters, dataConstructors')], constructors', values')
    renameDataConstructor (done, values) (name, identifier, argument) =
      let (values', name') = claim values name
       in (done <> [(name', identifier, argument)], values')

-- Ur elaborates @open M@ into ordinary projected declarations.  Besides
-- making names available to following declarations, those aliases are part of
-- the surrounding structure's inferred signature.  Merely importing the
-- signature into the environment loses opened exports such as a functor
-- result's @main@.
openSignatureDeclarations :: GlobalId -> [String] -> Signature -> Environment -> ([Decl], Environment)
openSignatureDeclarations root basePath signature environment =
  let at = locatedSpan signature
      project = projectConAt root basePath signature
      visible name = case name of
        [] -> False
        '?' : _ -> False
        _ -> True
      projectedNested name nested =
        projectSignatureAt root basePath signature (selfify root (basePath <> [name]) nested)
      declarations = case locatedValue signature of
        SgnConst items -> concatMap (openItem at project visible projectedNested) items
        _ -> []
      openedSignature = Located at (SgnConst (concatMap declarationSignature declarations))
      imported = importSignature Import openedSignature environment
      -- Values opened from a module are projections, not references to the
      -- signature item's nominal ID.  Keep that expression identity for later
      -- elaboration and instance search.
      withProjectedValues = foldl overrideValue imported declarations
   in (declarations, withProjectedValues)
  where
    overrideValue current declaration = case locatedValue declaration of
      DVal name identifier typ expression -> bindNamedValue name identifier typ expression current
      _ -> current
    openItem at project visible projectedNested item = case locatedValue item of
      SgiConAbs name identifier kind | visible name ->
        [Located at (DCon name identifier kind (Located at (CModProj root basePath name)))]
      SgiCon name identifier kind _ | visible name ->
        [Located at (DCon name identifier kind (Located at (CModProj root basePath name)))]
      SgiClassAbs name identifier kind | visible name ->
        [Located at (DCon name identifier kind (Located at (CModProj root basePath name)))]
      SgiClass name identifier kind _ | visible name ->
        [Located at (DCon name identifier kind (Located at (CModProj root basePath name)))]
      SgiDatatype definitions ->
        [ Located at (DDatatypeImp name identifier root basePath name parameters
            [(constructorName, constructorId, fmap project argument) | (constructorName, constructorId, argument) <- constructors])
        | (name, identifier, parameters, constructors) <- definitions
        , visible name
        ]
      SgiDatatypeImp name identifier original path originalName parameters constructors
        | visible name -> [Located at (DDatatypeImp name identifier original path originalName parameters
            [(constructorName, constructorId, fmap project argument) | (constructorName, constructorId, argument) <- constructors])]
      SgiVal name identifier typ | visible name ->
        [Located at (DVal name identifier (project typ) (Located at (EModProj root basePath name)))]
      SgiStr _ name identifier nested | visible name ->
        [Located at (DStr name identifier (projectedNested name nested)
          (Located at (StrProj (projectionStructure at root basePath) name)))]
      SgiSgn name identifier _ | visible name ->
        [Located at (DSgn name identifier (Located at (SgnProj root basePath name)))]
      SgiConstraint left right -> [Located at (DConstraint (project left) (project right))]
      _ -> []
    projectionStructure at identifier path =
      foldl (\parent name -> Located at (StrProj parent name)) (Located at (StrVar identifier)) path

-- Signature items retain the constructor IDs allocated while the signature
-- was elaborated.  When the signature describes a structure, constraints must
-- instead mention projections through that structure (the same substitution
-- used for projected value types).
openProjectedSignatureConstraints :: GlobalId -> [String] -> Signature -> Environment -> Signature -> ElabM Environment
openProjectedSignatureConstraints root basePath projectionSignature environment signature =
  case signatureItems environment signature of
    Nothing -> pure environment
    Just items -> foldM (openItem basePath) environment items
  where
    project = projectConAt root basePath projectionSignature
    openItem currentPath current item = case locatedValue item of
      SgiConstraint left right -> assertDisjoint current (project left) (project right)
      SgiClassAbs name _ _ -> pure (addProjectedClass currentPath name current)
      SgiClass name _ _ _ -> pure (addProjectedClass currentPath name current)
      SgiVal name _ typ ->
        pure (bindInstanceValue (project typ) (Located (locatedSpan item) (EModProj root currentPath name)) current)
      SgiStr Import name _ nested -> case signatureItems current nested of
        Just nestedItems -> foldM (openItem (currentPath <> [name])) current nestedItems
        Nothing -> pure current
      _ -> pure current
    addProjectedClass currentPath name current =
      let key = ClassProjected root currentPath name
       in current
            { environmentClasses = Set.insert key (environmentClasses current)
            , environmentOpenRules = Map.insertWith (<>) key [] (environmentOpenRules current)
            , environmentClosedRules = Map.insertWith (<>) key [] (environmentClosedRules current)
            }
