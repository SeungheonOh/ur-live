{-# LANGUAGE LambdaCase #-}

-- | Signature lookup, opening, selfification, and compatibility. These
-- operations live together because every namespace is traversed through
-- module paths in the same way.
module Vr.Elaborate.Modules
  ( headNormalizeSignature
  , signatureItems
  , projectConstructor
  , projectValue
  , projectStructure
  , projectSignature
  , projectDatatype
  , projectDataConstructor
  , projectDatatypeForConstructor
  , projectConAt
  , projectSignatureAt
  , resolveStructurePath
  , importSignature
  , selfify
  , subsignature
  ) where

import Control.Monad (foldM, forM_, unless)
import Control.Monad.State.Strict (get, put)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import qualified Data.Set as Set
import Vr.Elaborate.Classes (bindNamedValue, classHead)
import Vr.Elaborate.State
import Vr.Elaborate.Types
import Vr.Source (Explicitness (Implicit), Located (..), Span, noSpan)

headNormalizeSignature :: Environment -> Signature -> Signature
headNormalizeSignature environment signature = case locatedValue signature of
  SgnVar identifier -> maybe signature (headNormalizeSignature environment . signatureBindingSignature) (signatureById environment identifier)
  SgnProj moduleId path name ->
    maybe signature (headNormalizeSignature environment) $ do
      root <- structureById environment moduleId
      let rootSignature = headNormalizeSignature environment (structureBindingSignature root)
      (_, nested) <- descendSignature rootSignature path
      projected <- projectSignature nested name
      pure (projectSignatureAt moduleId path rootSignature projected)
  SgnWhere base path name definition -> replaceConstructor path name definition (headNormalizeSignature environment base)
  _ -> signature

signatureItems :: Environment -> Signature -> Maybe [SigItem]
signatureItems environment signature = case locatedValue (headNormalizeSignature environment signature) of
  SgnConst items -> Just items
  _ -> Nothing

projectConstructor :: Signature -> String -> Maybe ConBinding
projectConstructor signature name = listToMaybe $ do
  item <- constantItems signature
  case locatedValue item of
    SgiConAbs itemName identifier kind | itemName == name -> pure (ConBinding identifier kind Nothing False)
    SgiCon itemName identifier kind definition | itemName == name -> pure (ConBinding identifier kind (Just definition) False)
    SgiClassAbs itemName identifier kind | itemName == name -> pure (ConBinding identifier kind Nothing True)
    SgiClass itemName identifier kind definition | itemName == name -> pure (ConBinding identifier kind (Just definition) True)
    SgiDatatype definitions -> do
      (itemName, identifier, parameters, _) <- definitions
      if itemName == name then pure (ConBinding identifier (datatypeKind (locatedSpan item) parameters) Nothing False) else []
    SgiDatatypeImp itemName identifier original path originalName parameters _ | itemName == name ->
      pure (ConBinding identifier (datatypeKind (locatedSpan item) parameters)
        (Just (Located (locatedSpan item) (CModProj original path originalName))) False)
    _ -> []

projectValue :: Signature -> String -> Maybe ValueBinding
projectValue signature name = listToMaybe $ do
  item <- constantItems signature
  case locatedValue item of
    SgiVal itemName identifier typ | itemName == name -> pure (ValueBinding identifier typ (Located (locatedSpan item) (ENamed identifier)))
    SgiDatatype definitions -> do
      (_, typeId, parameters, constructors) <- definitions
      (itemName, identifier, argument) <- constructors
      if itemName == name
        then let typ = dataConstructorScheme (locatedSpan item) typeId parameters argument
              in pure (ValueBinding identifier typ (Located (locatedSpan item) (ENamed identifier)))
        else []
    SgiDatatypeImp _ typeId _ _ _ parameters constructors -> do
      (itemName, identifier, argument) <- constructors
      if itemName == name
        then let typ = dataConstructorScheme (locatedSpan item) typeId parameters argument
              in pure (ValueBinding identifier typ (Located (locatedSpan item) (ENamed identifier)))
        else []
    _ -> []

projectStructure :: Signature -> String -> Maybe (GlobalId, Signature)
projectStructure signature name = listToMaybe $ do
  item <- constantItems signature
  case locatedValue item of
    SgiStr _ itemName identifier nested | itemName == name -> pure (identifier, nested)
    _ -> []

projectSignature :: Signature -> String -> Maybe Signature
projectSignature signature name = listToMaybe $ do
  item <- constantItems signature
  case locatedValue item of
    SgiSgn itemName _ nested | itemName == name -> pure nested
    _ -> []

projectDatatype :: Signature -> String -> Maybe DatatypeBinding
projectDatatype signature name = listToMaybe $ do
  item <- constantItems signature
  case locatedValue item of
    SgiDatatype definitions -> do
      (itemName, typeId, parameters, constructors) <- definitions
      if itemName == name then pure (makeDatatype (locatedSpan item) typeId parameters constructors) else []
    SgiDatatypeImp itemName typeId _ _ _ parameters constructors | itemName == name ->
      pure (makeDatatype (locatedSpan item) typeId parameters constructors)
    _ -> []

projectDataConstructor :: Signature -> String -> Maybe DataConstructorBinding
projectDataConstructor signature name = listToMaybe $ do
  item <- constantItems signature
  case locatedValue item of
    SgiDatatype definitions -> do
      (_, typeId, parameters, constructors) <- definitions
      let datatypeClass = classifyDatatype constructors
      (itemName, identifier, argument) <- constructors
      if itemName == name
        then pure (DataConstructorBinding datatypeClass identifier typeId parameters argument (dataConstructorScheme (locatedSpan item) typeId parameters argument))
        else []
    SgiDatatypeImp _ typeId _ _ _ parameters constructors -> do
      let datatypeClass = classifyDatatype constructors
      (itemName, identifier, argument) <- constructors
      if itemName == name
        then pure (DataConstructorBinding datatypeClass identifier typeId parameters argument (dataConstructorScheme (locatedSpan item) typeId parameters argument))
        else []
    _ -> []

projectDatatypeForConstructor :: Signature -> String -> Maybe DatatypeBinding
projectDatatypeForConstructor signature constructorName = listToMaybe $ do
  item <- constantItems signature
  case locatedValue item of
    SgiDatatype definitions -> do
      (_, typeId, parameters, constructors) <- definitions
      if any (\(name, _, _) -> name == constructorName) constructors
        then pure (makeDatatype (locatedSpan item) typeId parameters constructors)
        else []
    SgiDatatypeImp _ typeId _ _ _ parameters constructors
      | any (\(name, _, _) -> name == constructorName) constructors ->
          pure (makeDatatype (locatedSpan item) typeId parameters constructors)
    _ -> []

-- | Substitute the abstract constructor identities bound by a signature with
-- projections through a particular structure path.  The reference performs
-- this substitution whenever it projects a value or datatype constructor;
-- storing the signature alone is not enough because its value types retain
-- their original named constructor IDs.
projectConAt :: GlobalId -> [String] -> Signature -> Con -> Con
projectConAt root basePath signature = mapCon
  where
    paths = collect basePath signature
    modulePaths = collectModules basePath signature
    collect path current = case locatedValue current of
      SgnConst items -> Map.unions (map (collectItem path) items)
      SgnWhere underlying _ _ _ -> collect path underlying
      _ -> Map.empty
    collectItem path item = case locatedValue item of
      SgiConAbs name identifier _ -> one identifier path name
      SgiCon name identifier _ _ -> one identifier path name
      SgiClassAbs name identifier _ -> one identifier path name
      SgiClass name identifier _ _ -> one identifier path name
      SgiDatatype definitions -> Map.fromList [(identifier, (path, name)) | (name, identifier, _, _) <- definitions]
      SgiDatatypeImp name identifier _ _ _ _ _ -> one identifier path name
      SgiStr _ name _ nested -> collect (path <> [name]) nested
      _ -> Map.empty
    one identifier path name = Map.singleton identifier (path, name)
    collectModules path current = case locatedValue current of
      SgnConst items -> Map.unions (map (collectModuleItem path) items)
      SgnWhere underlying _ _ _ -> collectModules path underlying
      _ -> Map.empty
    collectModuleItem path item = case locatedValue item of
      SgiStr _ name identifier nested ->
        Map.insert identifier (path <> [name]) (collectModules (path <> [name]) nested)
      _ -> Map.empty
    mapCon constructor = constructor {locatedValue = case locatedValue constructor of
      CNamed identifier -> case Map.lookup identifier paths of
        Just (path, name) -> CModProj root path name
        Nothing -> CNamed identifier
      CModProj identifier path name -> case Map.lookup identifier modulePaths of
        Just prefix -> CModProj root (prefix <> path) name
        Nothing -> CModProj identifier path name
      TFun domain range -> TFun (mapCon domain) (mapCon range)
      TCFun explicitness name kind body -> TCFun explicitness name kind (mapCon body)
      TRecord row -> TRecord (mapCon row)
      TDisjoint left right body -> TDisjoint (mapCon left) (mapCon right) (mapCon body)
      CApp function argument -> CApp (mapCon function) (mapCon argument)
      CAbs name kind body -> CAbs name kind (mapCon body)
      CKAbs name body -> CKAbs name (mapCon body)
      CKApp function kind -> CKApp (mapCon function) kind
      TKFun name body -> TKFun name (mapCon body)
      CRecord kind fields -> CRecord kind [(mapCon fieldName, mapCon value) | (fieldName, value) <- fields]
      CConcat left right -> CConcat (mapCon left) (mapCon right)
      CTuple elements -> CTuple (map mapCon elements)
      CProj tuple index -> CProj (mapCon tuple) index
      other -> other}

-- | Project references to constructors from an enclosing structure throughout
-- a nested signature.  In particular, a functor stored inside a structure may
-- mention constructors declared beside it.  Returning the nested signature
-- verbatim leaves those references as stale 'CNamed' IDs; Ur instead turns
-- them into paths through the structure being projected.
projectSignatureAt :: GlobalId -> [String] -> Signature -> Signature -> Signature
projectSignatureAt root basePath enclosing = mapSignature
  where
    project = projectConAt root basePath enclosing
    mapSignature signature = signature {locatedValue = case locatedValue signature of
      SgnConst items -> SgnConst (map mapItem items)
      SgnFun name identifier domain range ->
        SgnFun name identifier (mapSignature domain) (mapSignature range)
      SgnWhere underlying path name definition ->
        SgnWhere (mapSignature underlying) path name (project definition)
      other -> other}
    mapItem item = item {locatedValue = case locatedValue item of
      SgiConAbs name identifier kind ->
        case locatedValue (project (Located (locatedSpan item) (CNamed identifier))) of
          CModProj projectedRoot projectedPath projectedName ->
            SgiCon name identifier kind (Located (locatedSpan item) (CModProj projectedRoot projectedPath projectedName))
          _ -> SgiConAbs name identifier kind
      SgiCon name identifier kind definition ->
        SgiCon name identifier kind (project definition)
      SgiDatatype definitions ->
        case definitions of
          [(name, identifier, parameters, constructors)] ->
            case locatedValue (project (Located (locatedSpan item) (CNamed identifier))) of
              CModProj projectedRoot projectedPath projectedName ->
                SgiDatatypeImp name identifier projectedRoot projectedPath projectedName parameters
                  [ (constructorName, constructorId, fmap project argument)
                  | (constructorName, constructorId, argument) <- constructors
                  ]
              _ -> mappedDatatypes definitions
          _ -> mappedDatatypes definitions
      SgiDatatypeImp name identifier original path originalName parameters constructors ->
        SgiDatatypeImp name identifier original path originalName parameters
          [ (constructorName, constructorId, fmap project argument)
          | (constructorName, constructorId, argument) <- constructors
          ]
      SgiVal name identifier typ -> SgiVal name identifier (project typ)
      SgiStr mode name identifier nested -> SgiStr mode name identifier (mapSignature nested)
      SgiSgn name identifier nested -> SgiSgn name identifier (mapSignature nested)
      SgiConstraint left right -> SgiConstraint (project left) (project right)
      SgiClass name identifier kind definition ->
        SgiClass name identifier kind (project definition)
      SgiClassAbs name identifier kind ->
        case locatedValue (project (Located (locatedSpan item) (CNamed identifier))) of
          CModProj projectedRoot projectedPath projectedName ->
            SgiClass name identifier kind (Located (locatedSpan item) (CModProj projectedRoot projectedPath projectedName))
          _ -> SgiClassAbs name identifier kind}
    mappedDatatypes definitions = SgiDatatype
      [ (name, identifier, parameters,
          [ (constructorName, constructorId, fmap project argument)
          | (constructorName, constructorId, argument) <- constructors
          ])
      | (name, identifier, parameters, constructors) <- definitions
      ]

resolveStructurePath :: Environment -> [String] -> Maybe (GlobalId, [String], Signature)
resolveStructurePath environment path = case path of
  [] -> Nothing
  first : rest -> do
    binding <- Map.lookup first (environmentStructures environment)
    signature <- descend (structureBindingSignature binding) rest
    pure (structureBindingId binding, rest, headNormalizeSignature environment signature)
  where
    descend signature [] = Just (headNormalizeSignature environment signature)
    descend signature (name : names) = do
      (_, nested) <- projectStructure (headNormalizeSignature environment signature) name
      descend nested names

importSignature :: ImportMode -> Signature -> Environment -> Environment
importSignature mode signature environment = case signatureItems environment signature of
  Nothing -> environment
  Just items -> foldl importItem environment items
  where
    importItem current item = case locatedValue item of
      SgiConAbs name identifier kind -> addCon name identifier kind Nothing False current
      SgiCon name identifier kind definition -> addCon name identifier kind (Just definition) False current
      SgiClassAbs name identifier kind -> addCon name identifier kind Nothing True (markClass identifier Nothing current)
      SgiClass name identifier kind definition -> addCon name identifier kind (Just definition) True (markClass identifier (Just definition) current)
      SgiVal name identifier typ -> addValue name identifier typ current
      SgiSgn name identifier nested -> insertSignatureBinding name (SignatureBinding identifier nested) current
      SgiStr itemMode name identifier nested ->
        let withStructure = insertStructureBinding name (StructureBinding identifier nested) current
         in if mode == Import && itemMode == Import then importNestedInstances nested withStructure else withStructure
      SgiDatatype definitions -> foldl (importDatatype Nothing) current definitions
      SgiDatatypeImp {} -> importDatatypeImp current (locatedValue item)
      SgiConstraint {} -> current
    addCon name identifier kind definition isClass current =
      insertConBinding name (ConBinding identifier kind definition isClass) current
    addValue name identifier typ current =
      bindNamedValue name identifier typ (Located (locatedSpan signature) (ENamed identifier)) current
    markClass identifier definition current =
      current
        { environmentClasses = maybe id Set.insert (definition >>= classHead)
            (Set.insert (ClassNamed identifier) (environmentClasses current))
        }
    importNestedInstances _ current = current
    importDatatype definition current (name, typeId, parameters, constructors) =
      let kind = datatypeKind (locatedSpan signature) parameters
          binding = makeDatatype (locatedSpan signature) typeId parameters constructors
          current' = addCon name typeId kind definition False current
       in foldl (importDataCon (classifyDatatype constructors) typeId parameters) (current' {environmentDatatypes = Map.insert typeId binding (environmentDatatypes current')}) constructors
    importDatatypeImp current = \case
      SgiDatatypeImp name typeId original path originalName parameters constructors ->
        importDatatype (Just (Located (locatedSpan signature) (CModProj original path originalName))) current
          (name, typeId, parameters, constructors)
      _ -> current
    importDataCon datatypeClass typeId parameters current (name, identifier, argument) =
      let scheme = dataConstructorScheme (locatedSpan signature) typeId parameters argument
          dataBinding = DataConstructorBinding datatypeClass identifier typeId parameters argument scheme
       in current
            { environmentValues = Map.insert name (ValueBinding identifier scheme (Located (locatedSpan signature) (ENamed identifier))) (environmentValues current)
            , environmentDataConstructors = Map.insert name dataBinding (environmentDataConstructors current)
            }

selfify :: GlobalId -> [String] -> Signature -> Signature
selfify root initialPath signature = go initialPath signature
  where
    go path current = current {locatedValue = case locatedValue current of
      SgnConst items -> SgnConst (concatMap (selfItem path) items)
      other -> other}
    selfItem path item = case locatedValue item of
      SgiConAbs name identifier kind -> [item {locatedValue = SgiCon name identifier kind (project path name item)}]
      SgiDatatype definitions ->
        [ item {locatedValue = SgiDatatypeImp name identifier root path name parameters constructors}
        | (name, identifier, parameters, constructors) <- definitions
        ]
      SgiStr itemMode name identifier nested -> [item {locatedValue = SgiStr itemMode name identifier (go (path <> [name]) nested)}]
      SgiClassAbs name identifier kind -> [item {locatedValue = SgiClass name identifier kind (project path name item)}]
      _ -> [item]
    project path name item = Located (locatedSpan item) (CModProj root path name)

-- | Ordered signature compatibility. This is strict about namespaces and
-- requirement order; constructor comparison uses definitional equality.
subsignature :: Environment -> Span -> Signature -> Signature -> ElabM ()
subsignature environment at = subsignatureWith Map.empty environment
  where
    subsignatureWith inherited outerEnvironment actual expected =
      let actual' = headNormalizeSignature outerEnvironment actual
          expected' = headNormalizeSignature outerEnvironment expected
          comparisonEnvironment = importSignature Skip actual' outerEnvironment
       in case (locatedValue actual', locatedValue expected') of
            (SgnConst actualItems, SgnConst expectedItems) -> do
              let counterparts = collectCounterparts inherited actualItems expectedItems
                  comparisonEnvironment' = aliasCounterparts counterparts comparisonEnvironment
              forM_ expectedItems (matchItem comparisonEnvironment' counterparts actualItems)
            (SgnFun actualName actualId actualDomain actualRange, SgnFun _ expectedId expectedDomain expectedRange) -> do
              -- Functor arguments are contravariant, so the enclosing
              -- constructor correspondence reverses along with the two
              -- domain signatures.
              subsignatureWith (Map.fromList [(actualId', expectedId') | (expectedId', actualId') <- Map.toList inherited]) outerEnvironment expectedDomain actualDomain
              let alignedExpectedRange = replaceModuleId expectedId actualId expectedRange
                  rangeEnvironment = insertStructureBinding actualName (StructureBinding actualId (selfify actualId [] expectedDomain)) outerEnvironment
              subsignatureWith inherited rangeEnvironment actualRange alignedExpectedRange
            _ -> withSpanError "signature-form" at "Signature forms do not match"
    matchItem comparisonEnvironment counterparts actualItems requirement = case locatedValue requirement of
      SgiConAbs name _ expectedKind -> case findCon actualItems name of
        Nothing -> missing "constructor" name
        Just actualBinding -> unifyKind at (conBindingKind actualBinding) expectedKind
      SgiCon name _ expectedKind expectedDefinition -> case findCon actualItems name of
        Nothing -> missing "constructor" name
        Just actualBinding -> do
          unifyKind at (conBindingKind actualBinding) expectedKind
          case conBindingDefinition actualBinding of
            Nothing -> withSpanError "signature-abstract" at ("Constructor " <> name <> " is abstract")
            Just actualDefinition -> unifyCon comparisonEnvironment actualDefinition (rewriteCon counterparts expectedDefinition)
      SgiClassAbs name _ expectedKind -> matchClass comparisonEnvironment counterparts actualItems name expectedKind Nothing
      SgiClass name _ expectedKind definition -> matchClass comparisonEnvironment counterparts actualItems name expectedKind (Just definition)
      SgiVal name _ expectedType -> case findValue actualItems name of
        Nothing -> missing "value" name
        Just actualType -> do
          unifyCon comparisonEnvironment actualType (rewriteCon counterparts expectedType)
      SgiStr _ name expectedId nestedExpected -> case findStructure actualItems name of
        Nothing -> missing "structure" name
        Just (actualId, nestedActual) ->
          let nestedCounterparts = Map.insert expectedId actualId counterparts
           in subsignatureWith nestedCounterparts comparisonEnvironment nestedActual
                (rewriteSignatureHead nestedCounterparts nestedExpected)
      SgiSgn name _ nestedExpected -> case findSignature actualItems name of
        Nothing -> missing "signature" name
        Just (_, nestedActual) -> do
          let expected' = rewriteSignatureHead counterparts nestedExpected
          subsignatureWith counterparts comparisonEnvironment nestedActual expected'
          subsignatureWith counterparts comparisonEnvironment expected' nestedActual
      SgiDatatype definitions -> forM_ definitions $ \(name, _, parameters, _) -> case findDatatype actualItems name of
        Nothing -> missing "datatype" name
        Just found -> unless (datatypeBindingParameters found == parameters) (withSpanError "signature-datatype" at ("Datatype parameter mismatch for " <> name))
      SgiDatatypeImp name _ _ _ _ parameters _ -> case findDatatype actualItems name of
        Nothing -> missing "datatype" name
        Just found -> unless (datatypeBindingParameters found == parameters) (withSpanError "signature-datatype" at ("Datatype parameter mismatch for " <> name))
      SgiConstraint left right -> do
        let expectedLeft = rewriteCon counterparts left
            expectedRight = rewriteCon counterparts right
            candidates = [(actualLeft, actualRight) | item <- actualItems, SgiConstraint actualLeft actualRight <- [locatedValue item]]
        matched <- anyConstraint comparisonEnvironment expectedLeft expectedRight candidates
        unless matched (withSpanError "signature-constraint" at "Missing matching disjointness constraint")
    matchClass comparisonEnvironment counterparts actualItems name expectedKind definition = case findCon actualItems name of
      Nothing -> missing "class" name
      Just binding -> do
        unifyKind at (conBindingKind binding) expectedKind
        case (definition, conBindingDefinition binding) of
          (Just expectedDefinition, Just actualDefinition) -> unifyCon comparisonEnvironment actualDefinition (rewriteCon counterparts expectedDefinition)
          (Just _, Nothing) -> withSpanError "signature-abstract" at ("Class " <> name <> " is abstract")
          _ -> pure ()
    missing namespace name = withSpanError "signature-missing" at ("Missing " <> namespace <> " " <> name)

    -- The reference environment installs both IDs of every matched item while
    -- descending through a signature.  Keep those historical IDs reducible
    -- to the actual binding; this is essential for the reverse half of nested
    -- signature equivalence when an enclosing abstract type is implemented by
    -- a manifest constructor.
    aliasCounterparts counterparts environment' =
      environment'
        { environmentConstructorsById = foldl aliasCon (environmentConstructorsById environment') pairs
        , environmentSignaturesById = foldl aliasSignature (environmentSignaturesById environment') pairs
        , environmentStructuresById = foldl aliasStructure (environmentStructuresById environment') pairs
        }
      where
        pairs = Map.toList counterparts
        aliasCon bindings (expectedId, actualId) =
          maybe bindings (\binding -> Map.insert expectedId binding bindings) (Map.lookup actualId bindings)
        aliasSignature bindings (expectedId, actualId) =
          maybe bindings (\binding -> Map.insert expectedId binding bindings) (Map.lookup actualId bindings)
        aliasStructure bindings (expectedId, actualId) =
          maybe bindings (\binding -> Map.insert expectedId binding bindings) (Map.lookup actualId bindings)

    -- Constraints are unnamed.  Matching them must not commit speculative
    -- unification, since doing so can select and specialize the wrong item.
    anyConstraint _ _ _ [] = pure False
    anyConstraint comparisonEnvironment expectedLeft expectedRight ((actualLeft, actualRight) : rest) = do
      before <- get
      leftMatches <- conEqual comparisonEnvironment actualLeft expectedLeft
      rightMatches <- if leftMatches then conEqual comparisonEnvironment actualRight expectedRight else pure False
      put before
      if leftMatches && rightMatches
        then pure True
        else anyConstraint comparisonEnvironment expectedLeft expectedRight rest

    collectCounterparts initial actualItems = foldl collect initial
      where
        collect mappings requirement = case locatedValue requirement of
          SgiConAbs name expectedId _ -> constructor name expectedId mappings
          SgiCon name expectedId _ _ -> constructor name expectedId mappings
          SgiClassAbs name expectedId _ -> constructor name expectedId mappings
          SgiClass name expectedId _ _ -> constructor name expectedId mappings
          SgiDatatype definitions -> foldl datatypeMapping mappings definitions
          SgiDatatypeImp name expectedId _ _ _ _ _ -> datatypeName name expectedId mappings
          SgiStr _ name expectedId _ -> case findStructure actualItems name of
            Just (actualId, _) -> Map.insert expectedId actualId mappings
            Nothing -> mappings
          SgiSgn name expectedId _ -> case findSignature actualItems name of
            Just (actualId, _) -> Map.insert expectedId actualId mappings
            Nothing -> mappings
          _ -> mappings
        constructor name expectedId mappings = case findCon actualItems name of
          Just binding -> Map.insert expectedId (conBindingId binding) mappings
          Nothing -> mappings
        datatypeMapping mappings (name, expectedId, _, _) = datatypeName name expectedId mappings
        datatypeName name expectedId mappings = case findDatatype actualItems name of
          Just binding -> Map.insert expectedId (datatypeBindingId binding) mappings
          Nothing -> mappings

    rewriteCon counterparts constructor = constructor {locatedValue = case locatedValue constructor of
      CNamed identifier -> CNamed (Map.findWithDefault identifier identifier counterparts)
      CModProj identifier path name -> CModProj (Map.findWithDefault identifier identifier counterparts) path name
      TFun domain range -> TFun (go domain) (go range)
      TCFun explicitness name kind body -> TCFun explicitness name kind (go body)
      TRecord row -> TRecord (go row)
      TDisjoint left right body -> TDisjoint (go left) (go right) (go body)
      CApp function argument -> CApp (go function) (go argument)
      CAbs name kind body -> CAbs name kind (go body)
      CKAbs name body -> CKAbs name (go body)
      CKApp function kind -> CKApp (go function) kind
      TKFun name body -> TKFun name (go body)
      CRecord kind fields -> CRecord kind [(go fieldName, go value) | (fieldName, value) <- fields]
      CConcat left right -> CConcat (go left) (go right)
      CTuple elements -> CTuple (map go elements)
      CProj tuple index -> CProj (go tuple) index
      other -> other}
      where go = rewriteCon counterparts

    -- A projected or named signature head must be aligned before it can be
    -- normalized in the actual module environment.  Rewriting the complete
    -- signature here is too eager: functor domains are contravariant and
    -- reverse the enclosing correspondence themselves.
    rewriteSignatureHead counterparts signature = signature {locatedValue = case locatedValue signature of
      SgnVar identifier -> SgnVar (rewriteId identifier)
      SgnProj identifier path name -> SgnProj (rewriteId identifier) path name
      SgnWhere base path name definition ->
        SgnWhere (rewriteSignatureHead counterparts base) path name (rewriteCon counterparts definition)
      other -> other}
      where
        rewriteId identifier = Map.findWithDefault identifier identifier counterparts

    replaceModuleId old new signature = signature {locatedValue = case locatedValue signature of
      SgnConst items -> SgnConst (map replaceItem items)
      SgnFun name identifier domain range -> SgnFun name identifier (replaceModuleId old new domain) (replaceModuleId old new range)
      SgnWhere base path name definition -> SgnWhere (replaceModuleId old new base) path name (replaceCon definition)
      SgnProj identifier path name -> SgnProj (replaceId identifier) path name
      other -> other}
      where
        replaceId identifier = if identifier == old then new else identifier
        replaceItem item = item {locatedValue = case locatedValue item of
          SgiConAbs name identifier kind -> SgiConAbs name identifier kind
          SgiCon name identifier kind definition -> SgiCon name identifier kind (replaceCon definition)
          SgiClassAbs name identifier kind -> SgiClassAbs name identifier kind
          SgiClass name identifier kind definition -> SgiClass name identifier kind (replaceCon definition)
          SgiVal name identifier typ -> SgiVal name identifier (replaceCon typ)
          SgiSgn name identifier nested -> SgiSgn name identifier (replaceModuleId old new nested)
          SgiStr mode name identifier nested -> SgiStr mode name identifier (replaceModuleId old new nested)
          SgiDatatype definitions -> SgiDatatype [(name, identifier, parameters, [(constructorName, constructorId, fmap replaceCon argument) | (constructorName, constructorId, argument) <- constructors]) | (name, identifier, parameters, constructors) <- definitions]
          SgiDatatypeImp name identifier original path originalName parameters constructors -> SgiDatatypeImp name identifier (replaceId original) path originalName parameters [(constructorName, constructorId, fmap replaceCon argument) | (constructorName, constructorId, argument) <- constructors]
          SgiConstraint left right -> SgiConstraint (replaceCon left) (replaceCon right)
          }
        replaceCon constructor = constructor {locatedValue = case locatedValue constructor of
          CModProj identifier path name -> CModProj (replaceId identifier) path name
          TFun domain range -> TFun (replaceCon domain) (replaceCon range)
          TCFun explicitness name kind body -> TCFun explicitness name kind (replaceCon body)
          TRecord row -> TRecord (replaceCon row)
          TDisjoint left right body -> TDisjoint (replaceCon left) (replaceCon right) (replaceCon body)
          CApp function argument -> CApp (replaceCon function) (replaceCon argument)
          CAbs name kind body -> CAbs name kind (replaceCon body)
          CKAbs name body -> CKAbs name (replaceCon body)
          CKApp function kind -> CKApp (replaceCon function) kind
          TKFun name body -> TKFun name (replaceCon body)
          CRecord kind fields -> CRecord kind [(replaceCon fieldName, replaceCon value) | (fieldName, value) <- fields]
          CConcat left right -> CConcat (replaceCon left) (replaceCon right)
          CTuple elements -> CTuple (map replaceCon elements)
          CProj tuple index -> CProj (replaceCon tuple) index
          other -> other}

constantItems :: Signature -> [SigItem]
constantItems signature = case locatedValue signature of
  SgnConst items -> items
  _ -> []

descendSignature :: Signature -> [String] -> Maybe (GlobalId, Signature)
descendSignature signature path = foldM step (GlobalId (-1), signature) path
  where step (_, current) name = projectStructure current name

signatureById :: Environment -> GlobalId -> Maybe SignatureBinding
signatureById environment identifier = Map.lookup identifier (environmentSignaturesById environment)

structureById :: Environment -> GlobalId -> Maybe StructureBinding
structureById environment identifier = Map.lookup identifier (environmentStructuresById environment)

replaceConstructor :: [String] -> String -> Con -> Signature -> Signature
replaceConstructor path name definition signature = case (path, locatedValue signature) of
  ([], SgnConst items) -> signature {locatedValue = SgnConst (map replace items)}
  (next : rest, SgnConst items) -> signature {locatedValue = SgnConst (map (descend next rest) items)}
  _ -> signature
  where
    replace item = item {locatedValue = case locatedValue item of
      SgiConAbs itemName identifier kind | itemName == name -> SgiCon itemName identifier kind definition
      SgiCon itemName identifier kind _ | itemName == name -> SgiCon itemName identifier kind definition
      SgiClass itemName identifier kind _ | itemName == name -> SgiClass itemName identifier kind definition
      other -> other}
    descend next rest item = item {locatedValue = case locatedValue item of
      SgiStr itemMode itemName identifier nested | itemName == next -> SgiStr itemMode itemName identifier (replaceConstructor rest name definition nested)
      other -> other}

findCon :: [SigItem] -> String -> Maybe ConBinding
findCon items name = projectConstructor (Located (itemSpan items) (SgnConst items)) name

findValue :: [SigItem] -> String -> Maybe Con
findValue items name = valueBindingType <$> projectValue (Located (itemSpan items) (SgnConst items)) name

findStructure :: [SigItem] -> String -> Maybe (GlobalId, Signature)
findStructure items name = projectStructure (Located (itemSpan items) (SgnConst items)) name

findSignature :: [SigItem] -> String -> Maybe (GlobalId, Signature)
findSignature items name = listToMaybe
  [(identifier, signature) | item <- items, SgiSgn itemName identifier signature <- [locatedValue item], itemName == name]

findDatatype :: [SigItem] -> String -> Maybe DatatypeBinding
findDatatype items name = projectDatatype (Located (itemSpan items) (SgnConst items)) name

itemSpan :: [SigItem] -> Span
itemSpan (item : _) = locatedSpan item
itemSpan [] = noSpan

datatypeKind :: Span -> [String] -> Kind
datatypeKind at parameters = foldr (const (\result -> Located at (KArrow (Located at KType) result))) (Located at KType) parameters

dataConstructorScheme :: Span -> GlobalId -> [String] -> Maybe Con -> Con
dataConstructorScheme at typeId parameters argument = foldr quantify body parameters
  where
    result = foldl (\function index -> Located at (CApp function (Located at (CRel index)))) (Located at (CNamed typeId)) [length parameters - 1, length parameters - 2 .. 0]
    body = maybe result (\domain -> Located at (TFun domain result)) argument
    quantify name rest = Located at (TCFun Implicit name (Located at KType) rest)

makeDatatype :: Span -> GlobalId -> [String] -> [(String, GlobalId, Maybe Con)] -> DatatypeBinding
makeDatatype at typeId parameters constructors =
  DatatypeBinding typeId parameters
    [ (name, DataConstructorBinding (classifyDatatype constructors) identifier typeId parameters argument (dataConstructorScheme at typeId parameters argument))
    | (name, identifier, argument) <- constructors
    ]

classifyDatatype :: [(String, GlobalId, Maybe Con)] -> DatatypeKind
classifyDatatype constructors = case map (maybe False (const True) . third) constructors of
  [False, True] -> Option
  [True, False] -> Option
  arguments | not (or arguments) -> Enum
  _ -> Default
  where third (_, _, value) = value
