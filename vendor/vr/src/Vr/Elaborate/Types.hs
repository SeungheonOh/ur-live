{-# LANGUAGE LambdaCase #-}

module Vr.Elaborate.Types
  ( module Vr.Elaborate.Syntax
  , elaborateKind
  , checkKind
  , unifyKind
  , zonkKind
  , inferCon
  , checkCon
  , unifyCon
  , headNormalizeCon
  , zonkCon
  , conKind
  , substituteCon
  , substituteKindInCon
  , liftCon
  , liftConMetaDepth
  , pushRelativeKind
  , pushRelativeCon
  , lookupConstructor
  , lookupProjectedConstructor
  , kindEqual
  , conEqual
  ) where

import Control.Monad (foldM, forM, forM_, unless, zipWithM_)
import Control.Monad.State.Strict (get, gets, modify', put)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Maybe (listToMaybe)
import Vr.Elaborate.State
import Vr.Elaborate.Substitute
import Vr.Elaborate.Syntax
import qualified Vr.Source as S
import Vr.Source (Located (..), Span, mergeSpans)

elaborateKind :: S.SKind -> ElabM Kind
elaborateKind source = case S.locatedValue source of
  S.SKType -> pure (at KType)
  S.SKArrow domain range -> do
    domain' <- elaborateKind domain
    range' <- elaborateKind range
    pure (at (KArrow domain' range'))
  S.SKName -> pure (at KName)
  S.SKRecord element -> at . KRecord <$> elaborateKind element
  S.SKUnit -> pure (at KUnit)
  S.SKTuple elements -> at . KTuple <$> mapM elaborateKind elements
  S.SKWild -> freshKindMeta location "_"
  S.SKFun name body -> do
    body' <- withRelativeKind name (elaborateKind body)
    pure (at (KFun name body'))
  S.SKVar name -> do
    environment <- getEnvironment
    case relativeIndex name (environmentRelativeKinds environment) of
      Just index -> pure (at (KRel index))
      Nothing -> do
        withSpanError "unbound-kind" location ("Unbound kind variable " <> name)
        pure (at KError)
  where
    location = S.locatedSpan source
    at = Located location

checkKind :: S.SKind -> Kind -> ElabM Kind
checkKind source expected = do
  actual <- elaborateKind source
  unifyKind (S.locatedSpan source) actual expected
  pure actual

unifyKind :: Span -> Kind -> Kind -> ElabM ()
unifyKind at left0 right0 = do
  left <- zonkKind left0
  right <- zonkKind right0
  case (locatedValue left, locatedValue right) of
    (KError, _) -> pure ()
    (_, KError) -> pure ()
    (KMeta identifier _ _, _) -> solveKindMeta at identifier right
    (_, KMeta identifier _ _) -> solveKindMeta at identifier left
    (KTupleMeta identifier origin fields, KTuple elements) -> do
      forM_ fields $ \(index, expected) ->
        if index > 0 && index <= length elements
          then unifyKind at expected (elements !! (index - 1))
          else withSpanError "kind-tuple-projection" origin ("Tuple kind has no field " <> show index)
      writeKindMeta identifier right
    (KTuple elements, KTupleMeta identifier origin fields) ->
      unifyKind at (Located origin (KTupleMeta identifier origin fields)) (Located (locatedSpan left) (KTuple elements))
    (KTupleMeta first _ _, KTupleMeta second _ _) | first == second -> pure ()
    (KType, KType) -> pure ()
    (KName, KName) -> pure ()
    (KUnit, KUnit) -> pure ()
    (KArrow leftDomain leftRange, KArrow rightDomain rightRange) -> do
      unifyKind at leftDomain rightDomain
      unifyKind at leftRange rightRange
    (KRecord leftElement, KRecord rightElement) -> unifyKind at leftElement rightElement
    (KTuple leftElements, KTuple rightElements)
      | length leftElements == length rightElements -> zipWithM_ (unifyKind at) leftElements rightElements
    (KRel leftIndex, KRel rightIndex) | leftIndex == rightIndex -> pure ()
    (KFun _ leftBody, KFun _ rightBody) -> unifyKind at leftBody rightBody
    _ -> withSpanError "kind-mismatch" at ("Kind mismatch: " <> show left <> " versus " <> show right)

solveKindMeta :: Span -> MetaId -> Kind -> ElabM ()
solveKindMeta at identifier value = do
  same <- occursKind identifier value
  if same
    then case locatedValue value of
      KMeta other _ _ | other == identifier -> pure ()
      _ -> withSpanError "infinite-kind" at "Infinite kind"
    else writeKindMeta identifier value

occursKind :: MetaId -> Kind -> ElabM Bool
occursKind identifier kind0 = do
  kind <- zonkKind kind0
  case locatedValue kind of
    KMeta other _ _ -> pure (identifier == other)
    KTupleMeta other _ fields ->
      if identifier == other then pure True else or <$> mapM (occursKind identifier . snd) fields
    KArrow domain range -> (||) <$> occursKind identifier domain <*> occursKind identifier range
    KRecord element -> occursKind identifier element
    KTuple elements -> or <$> mapM (occursKind identifier) elements
    KFun _ body -> occursKind identifier body
    _ -> pure False

zonkKind :: Kind -> ElabM Kind
zonkKind kind = case locatedValue kind of
  KMeta identifier _ _ -> do
    solution <- readKindMeta identifier
    maybe (pure kind) zonkKind solution
  KTupleMeta identifier _ _ -> do
    solution <- readKindMeta identifier
    case solution of
      Nothing -> pure kind
      -- Open tuple kinds use their own metavariable as the identity of a
      -- mutable field set.  Adding another observed projection stores an
      -- updated descriptor under that identity; following it as an ordinary
      -- substitution would chase B -> KTupleMeta B forever.
      Just updated@(Located _ (KTupleMeta other _ _))
        | identifier == other -> pure updated
      Just updated -> zonkKind updated
  KArrow domain range -> do
    domain' <- zonkKind domain
    range' <- zonkKind range
    pure kind {locatedValue = KArrow domain' range'}
  KRecord element -> do
    element' <- zonkKind element
    pure kind {locatedValue = KRecord element'}
  KTuple elements -> do
    elements' <- mapM zonkKind elements
    pure kind {locatedValue = KTuple elements'}
  KFun name body -> do
    body' <- zonkKind body
    pure kind {locatedValue = KFun name body'}
  _ -> pure kind

inferCon :: S.SCon -> ElabM (Con, Kind)
inferCon source = case S.locatedValue source of
  S.SCAnnot constructor sourceKind -> do
    kind <- elaborateKind sourceKind
    constructor' <- checkCon constructor kind
    pure (constructor', kind)
  S.SCTFun domain range -> do
    domain' <- checkCon domain (at KType)
    range' <- checkCon range (at KType)
    pure (at (TFun domain' range'), at KType)
  S.SCTCFun explicitness name sourceKind body -> do
    kind <- elaborateKind sourceKind
    body' <- withRelativeCon name kind (checkCon body (at KType))
    pure (at (TCFun explicitness name kind body'), at KType)
  S.SCTRecord row -> do
    element <- freshKindMeta location "record"
    row' <- checkCon row (at (KRecord element))
    unifyKind location element (at KType)
    pure (at (TRecord row'), at KType)
  S.SCTDisjoint left right body -> do
    leftElement <- freshKindMeta location "disjoint-left"
    rightElement <- freshKindMeta location "disjoint-right"
    left' <- checkCon left (at (KRecord leftElement))
    right' <- checkCon right (at (KRecord rightElement))
    environment <- getEnvironment
    let assumed = assertDisjointRaw environment left' right'
    body' <- withEnvironmentLocal assumed (checkCon body (at KType))
    pure (at (TDisjoint left' right' body'), at KType)
  S.SCVar modules name -> inferConVariable location modules name
  S.SCApp function argument -> do
    (function', functionKind0) <- inferCon function
    functionKind <- zonkKind functionKind0
    case locatedValue functionKind of
      KArrow domain range -> do
        argument' <- checkCon argument domain
        pure (at (CApp function' argument'), range)
      KMeta {} -> do
        domain <- freshKindMeta location "argument"
        range <- freshKindMeta location "result"
        unifyKind location functionKind (at (KArrow domain range))
        argument' <- checkCon argument domain
        pure (at (CApp function' argument'), range)
      _ -> do
        withSpanError "constructor-application" location ("Constructor application of non-function kind " <> show functionKind)
        argument' <- fst <$> inferCon argument
        pure (at (CApp function' argument'), at KError)
  S.SCAbs name maybeSourceKind body -> do
    kind <- maybe (freshKindMeta location name) elaborateKind maybeSourceKind
    (body', bodyKind) <- withRelativeCon name kind (inferCon body)
    pure (at (CAbs name kind body'), at (KArrow kind bodyKind))
  S.SCKAbs name body -> do
    (body', bodyKind) <- withRelativeKind name (inferCon body)
    pure (at (CKAbs name body'), at (KFun name bodyKind))
  S.SCTKFun name body -> do
    body' <- withRelativeKind name (checkCon body (at KType))
    pure (at (TKFun name body'), at KType)
  S.SCName name -> pure (at (CName name), at KName)
  S.SCRecord fields -> do
    elementKind <- freshKindMeta location "row"
    fields' <- forM fields $ \(name, value) -> do
      name' <- checkCon name (at KName)
      value' <- checkCon value elementKind
      pure (name', value')
    environment <- getEnvironment
    addPairwiseDisjoint environment location elementKind fields'
    pure (at (CRecord elementKind fields'), at (KRecord elementKind))
  S.SCConcat left right -> do
    elementKind <- freshKindMeta location "row"
    let rowKind = at (KRecord elementKind)
    left' <- checkCon left rowKind
    right' <- checkCon right rowKind
    environment <- getEnvironment
    addConstraint (DisjointConstraint environment left' right' location)
    pure (at (CConcat left' right'), rowKind)
  S.SCMap -> do
    domain <- freshKindMeta location "map-domain"
    range <- freshKindMeta location "map-range"
    let mappingKind = at (KArrow domain range)
        resultKind = at (KArrow mappingKind (at (KArrow (at (KRecord domain)) (at (KRecord range)))))
    pure (at (CMap domain range), resultKind)
  S.SCUnit -> pure (at CUnit, at KUnit)
  S.SCTuple elements -> do
    inferred <- mapM inferCon elements
    pure (at (CTuple (map fst inferred)), at (KTuple (map snd inferred)))
  S.SCProj tuple index -> do
    (tuple', tupleKind0) <- inferCon tuple
    tupleKind <- zonkKind tupleKind0
    projectedKind <- case locatedValue tupleKind of
      KTuple elements
        | index > 0 && index <= length elements -> pure (elements !! (index - 1))
        | otherwise -> do
            withSpanError "constructor-projection" location ("Tuple constructor has no field " <> show index)
            pure (at KError)
      KTupleMeta identifier origin fields -> case lookup index fields of
        Just kind -> pure kind
        Nothing -> do
          kind <- freshKindMeta location ("tuple-" <> show index)
          writeKindMeta identifier (Located origin (KTupleMeta identifier origin ((index, kind) : fields)))
          pure kind
      KMeta {} -> do
        identifier <- freshMeta
        kind <- freshKindMeta location ("tuple-" <> show index)
        let tupleMeta = at (KTupleMeta identifier location [(index, kind)])
        unifyKind location tupleKind tupleMeta
        pure kind
      _ -> do
        withSpanError "constructor-projection" location "Projection from a non-tuple constructor"
        pure (at KError)
    pure (at (CProj tuple' index), projectedKind)
  S.SCWild sourceKind -> do
    kind <- elaborateKind sourceKind
    constructor <- freshConMeta location 0 kind "_"
    pure (constructor, kind)
  where
    location = S.locatedSpan source
    at = Located location

checkCon :: S.SCon -> Kind -> ElabM Con
checkCon source expected = do
  (constructor, actual) <- inferCon source
  unifyKind (S.locatedSpan source) actual expected
  pure constructor

inferConVariable :: Span -> [String] -> String -> ElabM (Con, Kind)
inferConVariable at modules name = do
  environment <- getEnvironment
  if null modules
    then case lookupRelativeCon name (environmentRelativeConstructors environment) of
      Just (index, binding) -> instantiateConHead at (Located at (CRel index)) (relativeConKind binding)
      Nothing -> case Map.lookup name (environmentConstructors environment) of
        Just binding -> instantiateConHead at (Located at (CNamed (conBindingId binding))) (conBindingKind binding)
        Nothing -> do
          withSpanError "unbound-constructor" at ("Unbound constructor " <> name)
          pure (Located at CError, Located at KError)
    else case lookupProjectedConstructor environment modules name of
      Just (moduleId, path, binding) ->
        instantiateConHead at (Located at (CModProj moduleId path name)) (conBindingKind binding)
      Nothing -> do
        withSpanError "unbound-constructor" at ("Unbound constructor " <> concatQualified modules name)
        pure (Located at CError, Located at KError)

-- Ur's surface language has kind abstraction but no surface kind-application
-- form for constructors.  Every constructor head is therefore instantiated at
-- fresh kinds until its head kind is no longer universally quantified.
instantiateConHead :: Span -> Con -> Kind -> ElabM (Con, Kind)
instantiateConHead at constructor kind0 = do
  kind <- zonkKind kind0
  case locatedValue kind of
    KFun _ body -> do
      argument <- freshKindMeta at "kind-argument"
      let constructor' = Located at (CKApp constructor argument)
          result = substituteKind 0 argument body
      instantiateConHead at constructor' result
    _ -> pure (constructor, kind)

lookupConstructor :: Environment -> GlobalId -> Maybe ConBinding
lookupConstructor environment identifier =
  Map.lookup identifier (environmentConstructorsById environment)

lookupProjectedConstructor :: Environment -> [String] -> String -> Maybe (GlobalId, [String], ConBinding)
lookupProjectedConstructor environment modules name = case modules of
  [] -> Nothing
  first : rest -> do
    structure <- Map.lookup first (environmentStructures environment)
    binding <- signatureConstructorAtNormalized environment (structureBindingSignature structure) rest name
    pure (structureBindingId structure, rest, binding)

signatureConstructorAtNormalized :: Environment -> Signature -> [String] -> String -> Maybe ConBinding
signatureConstructorAtNormalized environment signature path name = case path of
  [] -> signatureConstructor (normalizeSignatureHead environment signature) name
  next : rest -> do
    nested <- signatureStructure (normalizeSignatureHead environment signature) next
    signatureConstructorAtNormalized environment nested rest name

-- Types cannot import the module elaborator without creating a cycle, but
-- projected constructor lookup still needs to see through named/projected
-- signature aliases.  This is the head-normalization fragment needed by the
-- constructor namespace.
normalizeSignatureHead :: Environment -> Signature -> Signature
normalizeSignatureHead environment signature = case locatedValue signature of
  SgnVar identifier -> case signatureBindingById identifier of
    Just binding -> normalizeSignatureHead environment (signatureBindingSignature binding)
    Nothing -> signature
  SgnProj moduleId path name -> case structureBindingById moduleId of
    Nothing -> signature
    Just root -> case descend (structureBindingSignature root) path >>= (`signatureStructure` name) of
      Just nested -> normalizeSignatureHead environment nested
      Nothing -> signature
  _ -> signature
  where
    signatureBindingById identifier = Map.lookup identifier (environmentSignaturesById environment)
    structureBindingById identifier = Map.lookup identifier (environmentStructuresById environment)
    descend current [] = Just (normalizeSignatureHead environment current)
    descend current (piece : pieces) = do
      nested <- signatureStructure (normalizeSignatureHead environment current) piece
      descend nested pieces

signatureConstructor :: Signature -> String -> Maybe ConBinding
signatureConstructor signature name = case locatedValue signature of
  SgnConst items -> listToMaybe (mapMaybeItem items)
  _ -> Nothing
  where
    mapMaybeItem [] = []
    mapMaybeItem (item : rest) = case locatedValue item of
      SgiConAbs itemName identifier kind | itemName == name -> ConBinding identifier kind Nothing False : mapMaybeItem rest
      SgiCon itemName identifier kind definition | itemName == name -> ConBinding identifier kind (Just definition) False : mapMaybeItem rest
      SgiClassAbs itemName identifier kind | itemName == name -> ConBinding identifier kind Nothing True : mapMaybeItem rest
      SgiClass itemName identifier kind definition | itemName == name -> ConBinding identifier kind (Just definition) True : mapMaybeItem rest
      SgiDatatype definitions ->
        [ConBinding identifier (datatypeKind at arguments) Nothing False | (itemName, identifier, arguments, _) <- definitions, itemName == name]
          <> mapMaybeItem rest
      SgiDatatypeImp itemName identifier original path originalName arguments _ | itemName == name ->
        ConBinding identifier (datatypeKind at arguments)
          (Just (Located at (CModProj original path originalName))) False : mapMaybeItem rest
      _ -> mapMaybeItem rest
    at = locatedSpan signature

signatureStructure :: Signature -> String -> Maybe Signature
signatureStructure signature name = case locatedValue signature of
  SgnConst items -> listToMaybe [nested | item <- items, nested <- itemSignature item]
  _ -> Nothing
  where
    itemSignature item = case locatedValue item of
      SgiStr _ itemName _ nested | itemName == name -> [nested]
      _ -> []

datatypeKind :: Span -> [String] -> Kind
datatypeKind at arguments = foldr (\_ result -> Located at (KArrow (Located at KType) result)) (Located at KType) arguments

conKind :: Environment -> Con -> ElabM Kind
conKind environment constructor =
  headNormalizeCon environment constructor >>= conKindNormalized environment

-- The caller has already normalized this head against the current solution
-- table. Recursive queries still normalize their own inputs as usual.
conKindNormalized :: Environment -> Con -> ElabM Kind
conKindNormalized environment constructor = case locatedValue constructor of
  TFun {} -> pure (Located (locatedSpan constructor) KType)
  TCFun {} -> pure (Located (locatedSpan constructor) KType)
  TRecord {} -> pure (Located (locatedSpan constructor) KType)
  TDisjoint {} -> pure (Located (locatedSpan constructor) KType)
  CRel index -> case drop index (environmentRelativeConstructors environment) of
    binding : _ -> pure (relativeConKind binding)
    [] -> pure (Located (locatedSpan constructor) KError)
  CNamed identifier -> maybe (pure (Located (locatedSpan constructor) KError)) (pure . conBindingKind) (lookupConstructor environment identifier)
  CModProj moduleId path name -> lookupProjectedById environment moduleId path name >>= \case
    Just binding -> pure (conBindingKind binding)
    Nothing -> pure (Located (locatedSpan constructor) KError)
  CApp function _ -> do
    functionKind <- conKind environment function >>= zonkKind
    case locatedValue functionKind of
      KArrow _ range -> pure range
      _ -> pure (Located (locatedSpan constructor) KError)
  CAbs _ kind body -> Located (locatedSpan constructor) . KArrow kind <$> conKind (pushRelativeCon "_" kind environment) body
  CKAbs name body -> Located (locatedSpan constructor) . KFun name <$> conKind (pushRelativeKind name environment) body
  CKApp function argument -> do
    functionKind <- conKind environment function >>= zonkKind
    case locatedValue functionKind of
      KFun _ body -> pure (substituteKind 0 argument body)
      _ -> pure (Located (locatedSpan constructor) KError)
  TKFun {} -> pure (Located (locatedSpan constructor) KType)
  CName {} -> pure (Located (locatedSpan constructor) KName)
  CRecord kind _ -> pure (Located (locatedSpan constructor) (KRecord kind))
  CConcat left _ -> conKind environment left
  CMap domain range -> pure (Located (locatedSpan constructor) (KArrow (Located (locatedSpan constructor) (KArrow domain range)) (Located (locatedSpan constructor) (KArrow (Located (locatedSpan constructor) (KRecord domain)) (Located (locatedSpan constructor) (KRecord range))))))
  CUnit -> pure (Located (locatedSpan constructor) KUnit)
  CTuple elements -> Located (locatedSpan constructor) . KTuple <$> mapM (conKind environment) elements
  CProj tuple index -> do
    tupleKind <- conKind environment tuple >>= zonkKind
    case locatedValue tupleKind of
      KTuple elements | index > 0 && index <= length elements -> pure (elements !! (index - 1))
      _ -> pure (Located (locatedSpan constructor) KError)
  CError -> pure (Located (locatedSpan constructor) KError)
  CMeta _ _ kind _ -> pure kind

unifyCon :: Environment -> Con -> Con -> ElabM ()
unifyCon environment left0 right0 = do
  left <- headNormalizeCon environment left0
  right <- headNormalizeCon environment right0
  leftKind <- conKindNormalized environment left
  rightKind <- conKindNormalized environment right
  unifyKind (mergeSpans (locatedSpan left) (locatedSpan right)) leftKind rightKind
  kind <- zonkKind leftKind
  if locatedValue kind == KUnit
    then pure ()
    else unifyByShape kind left right
  where
    at = mergeSpans (locatedSpan left0) (locatedSpan right0)
    unifyByShape rowKind left right = case (locatedValue left, locatedValue right) of
      (CError, _) -> pure ()
      (_, CError) -> pure ()
      (CMeta leftId leftLevel _ _, CMeta rightId rightLevel _ _)
        | leftId == rightId && leftLevel == rightLevel -> pure ()
        | leftLevel == 0 -> solveMetaOrDelay rowKind left right leftId leftLevel
        | rightLevel == 0 -> solveMetaOrDelay rowKind right left rightId rightLevel
      (CMeta identifier level _ _, _) -> solveMetaOrDelay rowKind left right identifier level
      (_, CMeta identifier level _ _) -> solveMetaOrDelay rowKind right left identifier level
      (TFun leftDomain leftRange, TFun rightDomain rightRange) -> both leftDomain rightDomain leftRange rightRange
      (TCFun leftExplicitness leftName leftKind leftBody, TCFun rightExplicitness _ rightKind rightBody) -> do
        unless (leftExplicitness == rightExplicitness) (withSpanError "constructor-explicitness" at "Constructor quantifiers have different explicitness")
        unifyKind at leftKind rightKind
        unifyCon (pushRelativeCon leftName leftKind environment) leftBody rightBody
      (TRecord leftRow, TRecord rightRow) -> unifyCon environment leftRow rightRow
      (TDisjoint leftA leftB leftBody, TDisjoint rightA rightB rightBody) -> do
        unifyCon environment leftA rightA
        unifyCon environment leftB rightB
        unifyCon environment leftBody rightBody
      (CRel leftIndex, CRel rightIndex) | leftIndex == rightIndex -> pure ()
      (CNamed leftId, CNamed rightId) | leftId == rightId -> pure ()
      (CModProj leftId leftPath leftName, CModProj rightId rightPath rightName)
        | (leftId, leftPath, leftName) == (rightId, rightPath, rightName) -> pure ()
      (CApp leftFunction leftArgument, CApp rightFunction rightArgument) -> both leftFunction rightFunction leftArgument rightArgument
      (CAbs leftName leftKind leftBody, CAbs _ rightKind rightBody) -> unifyKind at leftKind rightKind >> unifyCon (pushRelativeCon leftName leftKind environment) leftBody rightBody
      (CKAbs leftName leftBody, CKAbs _ rightBody) -> unifyCon (pushRelativeKind leftName environment) leftBody rightBody
      (CKApp leftFunction leftKind, CKApp rightFunction rightKind) -> unifyCon environment leftFunction rightFunction >> unifyKind at leftKind rightKind
      (TKFun leftName leftBody, TKFun _ rightBody) -> unifyCon (pushRelativeKind leftName environment) leftBody rightBody
      (CName leftName, CName rightName) | leftName == rightName -> pure ()
      (CRecord leftElement leftFields, CRecord rightElement rightFields) -> do
        unifyKind at leftElement rightElement
        unifyKnownRows environment at leftFields rightFields
      (CRecord {}, _) -> addDelayedRow (DelayedRow environment rowKind left right at)
      (_, CRecord {}) -> addDelayedRow (DelayedRow environment rowKind left right at)
      (CConcat {}, _) -> addDelayedRow (DelayedRow environment rowKind left right at)
      (_, CConcat {}) -> addDelayedRow (DelayedRow environment rowKind left right at)
      (CMap leftDomain leftRange, CMap rightDomain rightRange) -> unifyKind at leftDomain rightDomain >> unifyKind at leftRange rightRange
      (CUnit, CUnit) -> pure ()
      (CTuple leftElements, CTuple rightElements) | length leftElements == length rightElements -> zipWithM_ (unifyCon environment) leftElements rightElements
      (CProj leftTuple leftIndex, _) -> unifyProjection rowKind leftTuple leftIndex right
      (_, CProj rightTuple rightIndex) -> unifyProjection rowKind rightTuple rightIndex left
      _ -> withSpanError "constructor-mismatch" at ("Constructor mismatch: " <> show left <> " versus " <> show right)
    both leftA rightA leftB rightB = unifyCon environment leftA rightA >> unifyCon environment leftB rightB
    solveMetaOrDelay rowKind meta value identifier level =
      case locatedValue rowKind of
        KRecord _ -> do
          recursive <- occursCon identifier value
          case (recursive, lowerCon level value) of
            (True, _) -> addDelayedRow (DelayedRow environment rowKind meta value at)
            (_, Nothing) -> addDelayedRow (DelayedRow environment rowKind meta value at)
            _ -> solveConMeta environment at identifier level value
        _ -> solveConMeta environment at identifier level value
    unifyProjection rowKind tuple index other = do
      tuple' <- headNormalizeCon environment tuple
      case locatedValue tuple' of
        CMeta identifier 0 tupleKind _ -> do
          tupleKind' <- zonkKind tupleKind
          case locatedValue tupleKind' of
            KTuple elements | index > 0 && index <= length elements -> do
              components <- mapM (\(componentIndex, componentKind) -> freshConMeta at 0 componentKind ("tuple-" <> show componentIndex)) (zip [(1 :: Int) ..] elements)
              solveConMeta environment at identifier 0 (Located at (CTuple components))
              unifyCon environment (components !! (index - 1)) other
            _ -> projectionFallback rowKind tuple' index other
        _ -> projectionFallback rowKind tuple' index other
    projectionFallback _ tuple index other = case locatedValue other of
      CProj otherTuple otherIndex | index == otherIndex -> unifyCon environment tuple otherTuple
      _ -> withSpanError "constructor-mismatch" at ("Constructor mismatch: " <> show (Located at (CProj tuple index)) <> " versus " <> show other)

unifyKnownRows :: Environment -> Span -> [(Con, Con)] -> [(Con, Con)] -> ElabM ()
unifyKnownRows environment at leftFields rightFields = do
  unmatched <- foldM match rightFields leftFields
  unless (null unmatched) (withSpanError "row-mismatch" at "Record rows have different fields")
  where
    match remaining (leftName, leftValue) = do
      matched <- findMatching leftName remaining
      case matched of
        Nothing -> withSpanError "row-field" at ("Missing record field " <> show leftName) >> pure remaining
        Just ((_, rightValue), rest) -> unifyCon environment leftValue rightValue >> pure rest
    findMatching _ [] = pure Nothing
    findMatching leftName (field@(rightName, _) : rest) = do
      equal <- conEqual environment leftName rightName
      if equal then pure (Just (field, rest)) else fmap (fmap (\(found, remainder) -> (found, field : remainder))) (findMatching leftName rest)

solveConMeta :: Environment -> Span -> MetaId -> Int -> Con -> ElabM ()
solveConMeta environment at identifier level value = do
  occurs <- occursCon identifier value
  if occurs
    then case locatedValue value of
      CMeta other otherLevel _ _ | other == identifier && otherLevel == level -> pure ()
      CMeta other _ _ _ | other == identifier -> withSpanError "constructor-scope" at "The same constructor inference variable occurs at incompatible binder depths"
      _ -> withSpanError "infinite-constructor" at "Infinite constructor"
    else do
      existing <- readConMeta identifier
      case existing of
        Nothing -> case lowerCon level value of
          Nothing -> withSpanError "constructor-scope" at "Constructor inference escaped the scope where it was created"
          Just solution -> do
            scope <- gets (IntMap.findWithDefault maxBound (unMetaId identifier) . elaborationConMetaScopes)
            if conEscapesNamedScope scope solution
              then withSpanError "constructor-scope" at "Constructor inference escaped the named scope where it was created"
              else writeConMeta identifier solution
        Just solution -> unifyCon environment (liftCon 0 level solution) value

occursCon :: MetaId -> Con -> ElabM Bool
occursCon identifier constructor0 = do
  constructor <- zonkCon constructor0
  pure (go constructor)
  where
    -- Zonk the entire tree once. This check cannot add solutions, so zonking
    -- each already-zonked descendant again only repeats the same traversal.
    go constructor = case locatedValue constructor of
      CMeta other _ _ _ -> identifier == other
      TFun domain range -> go domain || go range
      TCFun _ _ _ body -> go body
      TRecord row -> go row
      TDisjoint left right body -> go left || go right || go body
      CApp function argument -> go function || go argument
      CAbs _ _ body -> go body
      CKAbs _ body -> go body
      CKApp function _ -> go function
      TKFun _ body -> go body
      CRecord _ fields -> any (\(name, value) -> go name || go value) fields
      CConcat left right -> go left || go right
      CTuple elements -> any go elements
      CProj tuple _ -> go tuple
      _ -> False

headNormalizeCon :: Environment -> Con -> ElabM Con
headNormalizeCon environment = resolve Set.empty
  where
    -- Head normalization never commits metavariable solutions (its identity
    -- probe rolls back). Zonk the input and freshly expanded definitions, not
    -- every already-zonked descendant. Substitution still re-enters the full
    -- normalization rules; this only removes redundant solution-map walks.
    resolve visited constructor = zonkCon constructor >>= go visited
    go visited constructor = do
      case locatedValue constructor of
        CNamed identifier ->
          let key = (identifier, [], Nothing)
           in if Set.member key visited
                then pure constructor
                else case lookupConstructor environment identifier >>= conBindingDefinition of
                  Just definition | locatedValue definition /= CNamed identifier -> resolve (Set.insert key visited) definition
                  Nothing -> pure constructor
                  _ -> pure constructor
        CModProj moduleId path name ->
          let key = (moduleId, path, Just name)
           in if Set.member key visited
                then pure constructor
                else lookupProjectedById environment moduleId path name >>= \binding -> case binding >>= conBindingDefinition of
                  Just definition | locatedValue definition /= CModProj moduleId path name -> resolve (Set.insert key visited) definition
                  Nothing -> pure constructor
                  _ -> pure constructor
        CAbs name kind body -> do
          body' <- go visited body
          case locatedValue body' of
            CApp function argument
              | CRel 0 <- locatedValue argument
              , not (occursRelative 0 function) ->
                  go visited (substituteCon 0 (Located (locatedSpan constructor) CUnit) function)
            _ -> pure constructor {locatedValue = CAbs name kind body'}
        CApp function argument -> do
          function' <- go visited function
          case locatedValue function' of
            CAbs _ _ body -> go visited (substituteCon 0 argument body)
            CApp mapper mapping -> do
              mapper' <- go visited mapper
              case locatedValue mapper' of
                CMap domain range -> do
                  row <- go visited argument
                  case locatedValue row of
                    CRecord _ fields ->
                      go visited
                        (constructor {locatedValue = CRecord range [(name, constructor {locatedValue = CApp mapping value}) | (name, value) <- fields]})
                    CConcat left right ->
                      let mapped part = constructor {locatedValue = CApp function' part}
                       in go visited (constructor {locatedValue = CConcat (mapped left) (mapped right)})
                    CApp innerApplication innerRow -> do
                      identity <- mapFunctionIsIdentity visited domain mapping
                      if identity
                        then go visited row
                        else do
                          innerApplication' <- go visited innerApplication
                          case locatedValue innerApplication' of
                            CApp innerMapper innerFunction -> do
                              innerMapper' <- go visited innerMapper
                              case locatedValue innerMapper' of
                                CMap innerDomain _ ->
                                  let variable = constructor {locatedValue = CRel 0}
                                      innerValue = constructor {locatedValue = CApp (liftCon 0 1 innerFunction) variable}
                                      outerValue = constructor {locatedValue = CApp (liftCon 0 1 mapping) innerValue}
                                      composition = constructor {locatedValue = CAbs "v" innerDomain outerValue}
                                      fusedMap = constructor {locatedValue = CMap innerDomain range}
                                      fused = constructor {locatedValue = CApp (constructor {locatedValue = CApp fusedMap composition}) innerRow}
                                   in go visited fused
                                _ -> pure constructor {locatedValue = CApp function' row}
                            _ -> pure constructor {locatedValue = CApp function' row}
                    _ -> do
                      identity <- mapFunctionIsIdentity visited domain mapping
                      if identity then go visited row else pure constructor {locatedValue = CApp function' row}
                _ -> pure constructor {locatedValue = CApp function' argument}
            _ -> pure constructor {locatedValue = CApp function' argument}
        CKApp function kind -> do
          function' <- go visited function
          case locatedValue function' of
            CKAbs _ body -> go visited (substituteKindInCon 0 kind body)
            _ -> pure constructor {locatedValue = CKApp function' kind}
        CProj tuple index -> do
          tuple' <- go visited tuple
          case locatedValue tuple' of
            CTuple elements | index > 0 && index <= length elements -> go visited (elements !! (index - 1))
            _ -> pure constructor {locatedValue = CProj tuple' index}
        CConcat left right -> do
          left' <- go visited left
          right' <- go visited right
          case (locatedValue left', locatedValue right') of
            (CRecord kind leftFields, CRecord _ rightFields) ->
              pure constructor {locatedValue = CRecord kind (leftFields <> rightFields)}
            (CRecord _ [], _) -> pure right'
            (_, CRecord _ []) -> pure left'
            (CConcat first second, _) ->
              go visited (constructor {locatedValue = CConcat first (constructor {locatedValue = CConcat second right'})})
            _ -> pure constructor {locatedValue = CConcat left' right'}
        _ -> pure constructor

    -- Ur recognizes identity row maps extensionally.  This is important for
    -- abstract rows: @map (fn t => t) r@ must reduce to @r@ even though r's
    -- fields are not available.  Probe the mapping with a fresh constructor
    -- under a state snapshot, mirroring the reference compiler's unification
    -- variable test without committing probe solutions.
    mapFunctionIsIdentity visited domain mapping = do
      before <- get
      probe <- freshConMeta (locatedSpan mapping) 0 domain "map-identity"
      result <- go visited (Located (locatedSpan mapping) (CApp mapping probe)) >>= stripConstraints
      result' <- zonkCon result
      put before
      pure $ case locatedValue result' of
        CMeta identifier 0 _ _ -> case locatedValue probe of
          CMeta probeIdentifier 0 _ _ -> identifier == probeIdentifier
          _ -> False
        _ -> False
    stripConstraints value = case locatedValue value of
      TDisjoint _ _ body -> go Set.empty body >>= stripConstraints
      _ -> pure value
    occursRelative depth value = case locatedValue value of
      CRel index -> index == depth
      TFun domain range -> occursRelative depth domain || occursRelative depth range
      TCFun _ _ _ body -> occursRelative (depth + 1) body
      TRecord row -> occursRelative depth row
      TDisjoint left right body -> any (occursRelative depth) [left, right, body]
      CApp function argument -> occursRelative depth function || occursRelative depth argument
      CAbs _ _ body -> occursRelative (depth + 1) body
      CKAbs _ body -> occursRelative depth body
      CKApp function _ -> occursRelative depth function
      TKFun _ body -> occursRelative depth body
      CRecord _ fields -> any (\(fieldName, fieldValue) -> occursRelative depth fieldName || occursRelative depth fieldValue) fields
      CConcat left right -> occursRelative depth left || occursRelative depth right
      CTuple elements -> any (occursRelative depth) elements
      CProj tuple _ -> occursRelative depth tuple
      _ -> False

zonkCon :: Con -> ElabM Con
zonkCon constructor = case locatedValue constructor of
  CMeta identifier level _ _ -> do
    solution <- readConMeta identifier
    maybe (pure constructor) (zonkCon . liftCon 0 level) solution
  TFun domain range -> rebuild2 TFun domain range
  TCFun explicitness name kind body -> do
    kind' <- zonkKind kind
    body' <- zonkCon body
    pure constructor {locatedValue = TCFun explicitness name kind' body'}
  TRecord row -> rebuild1 TRecord row
  TDisjoint left right body -> do
    left' <- zonkCon left
    right' <- zonkCon right
    body' <- zonkCon body
    pure constructor {locatedValue = TDisjoint left' right' body'}
  CApp function argument -> rebuild2 CApp function argument
  CAbs name kind body -> do
    kind' <- zonkKind kind
    body' <- zonkCon body
    pure constructor {locatedValue = CAbs name kind' body'}
  CKAbs name body -> do
    body' <- zonkCon body
    pure constructor {locatedValue = CKAbs name body'}
  CKApp function kind -> do
    function' <- zonkCon function
    kind' <- zonkKind kind
    pure constructor {locatedValue = CKApp function' kind'}
  TKFun name body -> do
    body' <- zonkCon body
    pure constructor {locatedValue = TKFun name body'}
  CRecord kind fields -> do
    kind' <- zonkKind kind
    fields' <- mapM (\(name, value) -> (,) <$> zonkCon name <*> zonkCon value) fields
    pure constructor {locatedValue = CRecord kind' fields'}
  CConcat left right -> rebuild2 CConcat left right
  CMap domain range -> do
    domain' <- zonkKind domain
    range' <- zonkKind range
    pure constructor {locatedValue = CMap domain' range'}
  CTuple elements -> do
    elements' <- mapM zonkCon elements
    pure constructor {locatedValue = CTuple elements'}
  CProj tuple index -> do
    tuple' <- zonkCon tuple
    pure constructor {locatedValue = CProj tuple' index}
  _ -> pure constructor
  where
    rebuild1 make value = do
      value' <- zonkCon value
      pure constructor {locatedValue = make value'}
    rebuild2 make left right = do
      left' <- zonkCon left
      right' <- zonkCon right
      pure constructor {locatedValue = make left' right'}

kindEqual :: Kind -> Kind -> ElabM Bool
kindEqual left right = do
  left' <- zonkKind left
  right' <- zonkKind right
  pure (left' == right')

conEqual :: Environment -> Con -> Con -> ElabM Bool
conEqual environment left right = do
  before <- get
  unifyCon environment left right
  after <- get
  if length (elaborationDiagnosticsRev before) == length (elaborationDiagnosticsRev after)
    then pure True
    else put before >> pure False

pushRelativeKind :: String -> Environment -> Environment
pushRelativeKind name environment =
  environment
    { environmentRelativeKinds = name : environmentRelativeKinds environment
    , environmentRelativeConstructors =
        [binding {relativeConKind = liftKind 0 1 (relativeConKind binding)} | binding <- environmentRelativeConstructors environment]
    , environmentRelativeValues =
        [binding {relativeValueType = liftKindInCon 0 1 (relativeValueType binding)} | binding <- environmentRelativeValues environment]
    , environmentOpenRules = fmap (map liftKindRule) (environmentOpenRules environment)
    }
  where
    liftKindRule rule =
      rule
        { instanceQuantified = [(argument, liftKind 0 1 kind) | (argument, kind) <- instanceQuantified rule]
        , instanceHypotheses = map (liftKindInCon 0 1) (instanceHypotheses rule)
        , instanceConclusion = liftKindInCon 0 1 (instanceConclusion rule)
        , instanceDictionary = liftKindInExpr 0 1 (instanceDictionary rule)
        }

pushRelativeCon :: String -> Kind -> Environment -> Environment
pushRelativeCon name kind environment =
  environment
    { environmentRelativeConstructors = RelativeCon name kind : environmentRelativeConstructors environment
    , environmentRelativeValues =
        [binding {relativeValueType = liftCon 0 1 (relativeValueType binding)} | binding <- environmentRelativeValues environment]
    , environmentOpenRules = fmap (map liftConRule) (environmentOpenRules environment)
    , environmentDisjointFacts = Map.fromListWith Set.union
        [(shiftDisjointAtom left, Set.map shiftDisjointAtom rights) | (left, rights) <- Map.toList (environmentDisjointFacts environment)]
    }
  where
    liftConRule rule =
      rule
        { instanceHypotheses = map (liftCon 0 1) (instanceHypotheses rule)
        , instanceConclusion = liftCon 0 1 (instanceConclusion rule)
        , instanceDictionary = liftConInExpr 0 1 (instanceDictionary rule)
        }

shiftDisjointAtom :: DisjointAtom -> DisjointAtom
shiftDisjointAtom atom = case atom of
  DisjointRelativeName index projections -> DisjointRelativeName (index + 1) projections
  DisjointRelativeRow index projections -> DisjointRelativeRow (index + 1) projections
  _ -> atom

withRelativeKind :: String -> ElabM value -> ElabM value
withRelativeKind name action = scopedEnvironment $ modifyEnvironment (pushRelativeKind name) >> action

withRelativeCon :: String -> Kind -> ElabM value -> ElabM value
withRelativeCon name kind action = scopedEnvironment $ modifyEnvironment (pushRelativeCon name kind) >> action

lookupRelativeCon :: String -> [RelativeCon] -> Maybe (Int, RelativeCon)
lookupRelativeCon name = go 0
  where
    go _ [] = Nothing
    go index (binding : rest)
      | relativeConName binding == name = Just (index, binding)
      | otherwise = go (index + 1) rest

relativeIndex :: Eq value => value -> [value] -> Maybe Int
relativeIndex target = go 0
  where
    go _ [] = Nothing
    go index (value : rest)
      | value == target = Just index
      | otherwise = go (index + 1) rest

lookupProjectedById :: Environment -> GlobalId -> [String] -> String -> ElabM (Maybe ConBinding)
lookupProjectedById environment moduleId path name = case Map.lookup moduleId (environmentStructuresById environment) of
  Nothing -> pure Nothing
  Just structure -> do
    let rootSignature = normalizeSignatureHead environment (structureBindingSignature structure)
    projectionIndex <- projectionIndexFor environment moduleId rootSignature
    pure (projectBinding moduleId projectionIndex <$> Map.lookup (path, name) (projectionBindings projectionIndex))

projectBinding :: GlobalId -> ProjectionIndex -> ConBinding -> ConBinding
projectBinding moduleId projectionIndex binding = binding
  -- A nested definition may mention constructors in any enclosing signature.
  -- Project through the whole root signature so, for example, M.S.u = M.t is
  -- retained; using only S's signature leaks the old named identity allocated
  -- for the outer t.
  { conBindingDefinition =
      fmap (projectConWithIndex moduleId projectionIndex) (conBindingDefinition binding)
  }

conEscapesNamedScope :: Int -> Con -> Bool
conEscapesNamedScope scope constructor = case locatedValue constructor of
  CNamed identifier -> unGlobalId identifier >= scope
  CModProj identifier _ _ -> unGlobalId identifier >= scope
  TFun domain range -> descend [domain, range]
  TCFun _ _ _ body -> conEscapesNamedScope scope body
  TRecord row -> conEscapesNamedScope scope row
  TDisjoint left right body -> descend [left, right, body]
  CApp function argument -> descend [function, argument]
  CAbs _ _ body -> conEscapesNamedScope scope body
  CKAbs _ body -> conEscapesNamedScope scope body
  CKApp function _ -> conEscapesNamedScope scope function
  TKFun _ body -> conEscapesNamedScope scope body
  CRecord _ fields -> any (\(name, value) -> conEscapesNamedScope scope name || conEscapesNamedScope scope value) fields
  CConcat left right -> descend [left, right]
  CTuple elements -> descend elements
  CProj tuple _ -> conEscapesNamedScope scope tuple
  _ -> False
  where
    descend = any (conEscapesNamedScope scope)

projectionIndexFor
  :: Environment
  -> GlobalId
  -> Signature
  -> ElabM ProjectionIndex
projectionIndexFor environment root signature = do
  cached <- gets (Map.lookup root . elaborationProjectionIndexes)
  case cached of
    Just index -> pure index
    Nothing -> do
      let index = signatureProjectionIndex environment [] signature
      modify' (\state -> state
        { elaborationProjectionIndexes = Map.insert root index (elaborationProjectionIndexes state)
        })
      pure index

signatureProjectionIndex
  :: Environment
  -> [String]
  -> Signature
  -> ProjectionIndex
signatureProjectionIndex environment basePath signature =
  (collect basePath signature) {projectionBindings = collectBindings basePath signature}
  where
    collect path current = case locatedValue current of
      SgnConst items -> foldl' (collectItem path) emptyProjectionIndex items
      SgnWhere underlying _ _ _ ->
        let underlyingIndex = collect path underlying
         in underlyingIndex {projectionBindings = Map.empty}
      _ -> emptyProjectionIndex
    collectItem path collected item = case locatedValue item of
      SgiConAbs itemName identifier _ -> insertConstructorPath path itemName identifier collected
      SgiCon itemName identifier _ _ -> insertConstructorPath path itemName identifier collected
      SgiClassAbs itemName identifier _ -> insertConstructorPath path itemName identifier collected
      SgiClass itemName identifier _ _ -> insertConstructorPath path itemName identifier collected
      SgiDatatype definitions ->
        foldl' (\index (itemName, identifier, _, _) ->
          insertConstructorPath path itemName identifier index)
          collected definitions
      SgiDatatypeImp itemName identifier _ _ _ _ _ ->
        insertConstructorPath path itemName identifier collected
      SgiStr _ itemName identifier nested ->
        let nestedPath = path <> [itemName]
            nestedIndex = collect nestedPath nested
         in ProjectionIndex
              { projectionConstructorPaths = Map.union
                  (projectionConstructorPaths collected) (projectionConstructorPaths nestedIndex)
              , projectionStructurePaths = Map.union
                  (projectionStructurePaths collected)
                  (Map.insert identifier nestedPath (projectionStructurePaths nestedIndex))
              , projectionBindings = Map.union
                  (projectionBindings collected) (projectionBindings nestedIndex)
              }
      _ -> collected
    insertConstructorPath path itemName identifier index = index
      { projectionConstructorPaths = Map.insertWith (\_ existing -> existing)
          identifier (path, itemName) (projectionConstructorPaths index)
      }
    emptyProjectionIndex = ProjectionIndex Map.empty Map.empty Map.empty
    collectBindings path current =
      let normalized = normalizeSignatureHead environment current
       in case locatedValue normalized of
            SgnConst items -> foldl' (collectBindingItem (locatedSpan normalized) path) Map.empty items
            _ -> Map.empty
    collectBindingItem at path bindings item = case locatedValue item of
      SgiConAbs itemName identifier kind ->
        insertBinding path itemName (ConBinding identifier kind Nothing False) bindings
      SgiCon itemName identifier kind definition ->
        insertBinding path itemName (ConBinding identifier kind (Just definition) False) bindings
      SgiClassAbs itemName identifier kind ->
        insertBinding path itemName (ConBinding identifier kind Nothing True) bindings
      SgiClass itemName identifier kind definition ->
        insertBinding path itemName (ConBinding identifier kind (Just definition) True) bindings
      SgiDatatype definitions -> foldl' (\currentBindings (itemName, identifier, arguments, _) ->
        insertBinding path itemName
          (ConBinding identifier (datatypeKind at arguments) Nothing False)
          currentBindings) bindings definitions
      SgiDatatypeImp itemName identifier original originalPath originalName arguments _ ->
        insertBinding path itemName
          (ConBinding identifier (datatypeKind at arguments)
            (Just (Located at (CModProj original originalPath originalName))) False)
          bindings
      SgiStr _ itemName _ nested ->
        Map.union bindings (collectBindings (path <> [itemName]) nested)
      _ -> bindings
    insertBinding path itemName =
      Map.insertWith (\_ existing -> existing) (path, itemName)

projectConWithIndex
  :: GlobalId
  -> ProjectionIndex
  -> Con
  -> Con
projectConWithIndex root projectionIndex = mapCon
  where
    paths = projectionConstructorPaths projectionIndex
    modulePaths = projectionStructurePaths projectionIndex
    mapCon constructor = constructor {locatedValue = case locatedValue constructor of
      CNamed identifier -> case Map.lookup identifier paths of
        Just (path, itemName) -> CModProj root path itemName
        Nothing -> CNamed identifier
      CModProj identifier path itemName -> case Map.lookup identifier modulePaths of
        Just prefix -> CModProj root (prefix <> path) itemName
        Nothing -> CModProj identifier path itemName
      TFun domain range -> TFun (mapCon domain) (mapCon range)
      TCFun explicitness itemName kind body -> TCFun explicitness itemName kind (mapCon body)
      TRecord row -> TRecord (mapCon row)
      TDisjoint left right body -> TDisjoint (mapCon left) (mapCon right) (mapCon body)
      CApp function argument -> CApp (mapCon function) (mapCon argument)
      CAbs itemName kind body -> CAbs itemName kind (mapCon body)
      CKAbs itemName body -> CKAbs itemName (mapCon body)
      CKApp function kind -> CKApp (mapCon function) kind
      TKFun itemName body -> TKFun itemName (mapCon body)
      CRecord kind fields -> CRecord kind [(mapCon fieldName, mapCon value) | (fieldName, value) <- fields]
      CConcat left right -> CConcat (mapCon left) (mapCon right)
      CTuple elements -> CTuple (map mapCon elements)
      CProj tuple index -> CProj (mapCon tuple) index
      other -> other}

concatQualified :: [String] -> String -> String
concatQualified modules name = foldr (\piece suffix -> piece <> "." <> suffix) name modules

addPairwiseDisjoint :: Environment -> Span -> Kind -> [(Con, Con)] -> ElabM ()
addPairwiseDisjoint environment at element = go
  where
    go [] = pure ()
    go (field : rest) = do
      let singleton (name, value) = Located at (CRecord element [(name, value)])
      mapM_ (\other -> addConstraint (DisjointConstraint environment (singleton field) (singleton other) at)) rest
      go rest

withEnvironmentLocal :: Environment -> ElabM value -> ElabM value
withEnvironmentLocal environment action = do
  previous <- getEnvironment
  putEnvironment environment
  value <- action
  putEnvironment previous
  pure value

assertDisjointRaw :: Environment -> Con -> Con -> Environment
assertDisjointRaw environment left right =
  environment {environmentDisjointFacts = foldl addRight (foldl addLeft facts leftPieces) rightPieces}
  where
    facts = environmentDisjointFacts environment
    leftPieces = decomposeRaw left
    rightPieces = decomposeRaw right
    addLeft current piece = Map.insertWith Set.union piece (Set.fromList (filterAgainst piece rightPieces)) current
    addRight current piece = Map.insertWith Set.union piece (Set.fromList (filterAgainst piece leftPieces)) current
    filterAgainst DisjointName {} = filter (\case DisjointName {} -> False; _ -> True)
    filterAgainst _ = id

decomposeRaw :: Con -> [DisjointAtom]
decomposeRaw constructor = case locatedValue constructor of
  CRecord _ fields -> concatMap (namePiece . fst) fields
  CConcat left right -> decomposeRaw left <> decomposeRaw right
  CMeta identifier _ _ _ -> [DisjointMeta identifier []]
  CRel index -> [DisjointRelativeRow index []]
  CNamed identifier -> [DisjointNamedRow identifier []]
  CModProj identifier path name -> [DisjointProjectedRow identifier path name []]
  CApp outer row -> case locatedValue outer of
    CApp mapper _ | CMap {} <- locatedValue mapper -> decomposeRaw row
    _ -> []
  _ -> []
  where
    namePiece name = case locatedValue name of
      CName value -> [DisjointName value []]
      CMeta identifier _ _ _ -> [DisjointMeta identifier []]
      CRel index -> [DisjointRelativeName index []]
      CNamed identifier -> [DisjointNamedName identifier []]
      CModProj identifier path value -> [DisjointProjectedName identifier path value []]
      _ -> []
