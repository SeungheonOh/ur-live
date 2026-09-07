module Vr.Elaborate.Expression
  ( inferExpression
  , allowableRecursive
  , checkPatternExhaustiveness
  , isClassLike
  ) where

import Control.Applicative ((<|>))
import Control.Monad (forM, unless, when)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import qualified Data.Set as Set
import Vr.Elaborate.Classes
import Vr.Elaborate.Context
import Vr.Elaborate.Disjoint
import Vr.Elaborate.Modules
import Vr.Elaborate.Patterns
import Vr.Elaborate.Records
import Vr.Elaborate.State
import Vr.Elaborate.Types
import qualified Vr.Source as S
import Vr.Source (Explicitness (..), Inference (..), Located (..), Span)

inferExpression :: Environment -> S.SExpr -> ElabM (Expr, Con)
inferExpression environment source = withEnvironment environment $ case locatedValue source of
  S.SEAnnot expression sourceType -> do
    (expression', actualType) <- inferExpression environment expression
    expectedType <- checkCon sourceType (at KType)
    unifyCon environment actualType expectedType
    pure (expression', expectedType)
  S.SEPrim primitive -> (,) (at (EPrim primitive)) <$> primitiveType environment location primitive
  S.SEVar modules name inference -> do
    lookedUp <- lookupValue environment modules name
    case lookedUp of
      Nothing -> do
        withSpanError "unbound-value" location ("Unbound value " <> qualify modules name)
        pure (at EError, at CError)
      Just (expression, typ) -> elaborateHead environment inference expression typ
  S.SEApp function argument -> do
    (function', functionType) <- inferExpression environment function
    (argument', argumentType) <- inferExpression environment argument
    domain <- freshConMeta location 0 (at KType) "function-domain"
    range <- freshConMeta location 0 (at KType) "function-range"
    unifyCon environment functionType (at (TFun domain range))
    unifyCon environment argumentType domain
    let application = at (EApp function' argument')
    case findInference function of
      Nothing -> pure (application, range)
      Just inference -> elaborateHead environment inference application range
  S.SEAbs name annotation body -> do
    domain <- case annotation of
      Nothing -> freshConMeta location 0 (at KType) name
      Just sourceType -> checkCon sourceType (at KType)
    let bodyEnvironment = bindRelativeValue name domain environment
    (body', range) <- inferExpression bodyEnvironment body
    pure (at (EAbs name domain range body'), at (TFun domain range))
  S.SECApp expression constructor -> do
    (expression', expressionType0) <- inferExpression environment expression
    (constructor', constructorKind) <- inferCon constructor
    expressionType <- headNormalizeCon environment expressionType0
    case locatedValue expressionType of
      TCFun _ _ expectedKind body -> do
        unifyKind location constructorKind expectedKind
        let result = substituteCon 0 constructor' body
            application = at (ECApp expression' constructor')
        case findInference expression of
          Nothing -> pure (application, result)
          Just inference -> elaborateHead environment inference application result
      _ -> do
        withSpanError "constructor-application" location ("Explicit constructor application of non-polymorphic expression with type " <> show expressionType)
        pure (at EError, at CError)
  S.SECAbs explicitness name sourceKind body -> do
    kind <- elaborateKind sourceKind
    let bodyEnvironment = pushRelativeCon name kind environment
    (body', bodyType) <- inferExpression bodyEnvironment body
    pure (at (ECAbs explicitness name kind body'), at (TCFun explicitness name kind bodyType))
  S.SEDisjoint left right body -> do
    leftElement <- freshKindMeta location "disjoint-left"
    rightElement <- freshKindMeta location "disjoint-right"
    left' <- withEnvironment environment (checkCon left (at (KRecord leftElement)))
    right' <- withEnvironment environment (checkCon right (at (KRecord rightElement)))
    bodyEnvironment <- assertDisjoint environment left' right'
    (body', bodyType) <- inferExpression bodyEnvironment body
    pure (body', at (TDisjoint left' right' bodyType))
  S.SEDisjointApp expression -> do
    (expression', expressionType0) <- inferExpression environment expression
    expressionType <- headNormalizeCon environment expressionType0
    case locatedValue expressionType of
      TDisjoint left right body -> requireDisjoint environment left right location >> pure (expression', body)
      _ -> withSpanError "disjoint-application" location "Disjointness application requires a disjointness-qualified value" >> pure (at EError, at CError)
  S.SEKAbs name body -> do
    let bodyEnvironment = pushRelativeKind name environment
    (body', bodyType) <- inferExpression bodyEnvironment body
    pure (at (EKAbs name body'), at (TKFun name bodyType))
  S.SERecord fields flexible -> do
    when flexible (withSpanError "flexible-record-expression" location "Flexible record syntax is allowed only in patterns")
    fields' <- forM fields $ \(name, value) -> do
      name' <- withEnvironment environment (checkCon name (at KName))
      (value', typ) <- inferExpression environment value
      pure (name', value', typ)
    let row = at (CRecord (at KType) [(name, typ) | (name, _, typ) <- fields'])
    requireFieldDisjointness environment location (at KType) [(name, typ) | (name, _, typ) <- fields']
    pure (at (ERecord fields'), at (TRecord row))
  S.SEField record name -> do
    (record', recordType) <- inferExpression environment record
    name' <- withEnvironment environment (checkCon name (at KName))
    normalizedRecord <- headNormalizeCon environment recordType
    known <- case locatedValue normalizedRecord of
      TRecord row -> lookupRowField environment row name'
      _ -> pure Nothing
    case known of
      Just (field, rest) -> pure (at (EField record' name' field rest), field)
      Nothing -> do
        field <- freshConMeta location 0 (at KType) "field"
        rest <- freshConMeta location 0 (at (KRecord (at KType))) "field-rest"
        let first = at (CRecord (at KType) [(name', field)])
        unifyCon environment recordType (at (TRecord (at (CConcat first rest))))
        requireDisjoint environment first rest location
        pure (at (EField record' name' field rest), field)
  S.SEConcat left right -> do
    (left', leftType) <- inferExpression environment left
    (right', rightType) <- inferExpression environment right
    leftRow <- freshConMeta location 0 (at (KRecord (at KType))) "left-row"
    rightRow <- freshConMeta location 0 (at (KRecord (at KType))) "right-row"
    unifyCon environment leftType (at (TRecord leftRow))
    unifyCon environment rightType (at (TRecord rightRow))
    requireDisjoint environment leftRow rightRow location
    pure (at (EConcat left' leftRow right' rightRow), at (TRecord (at (CConcat leftRow rightRow))))
  S.SECut record name -> do
    (record', recordType) <- inferExpression environment record
    name' <- withEnvironment environment (checkCon name (at KName))
    field <- freshConMeta location 0 (at KType) "cut-field"
    rest <- freshConMeta location 0 (at (KRecord (at KType))) "cut-rest"
    let first = at (CRecord (at KType) [(name', field)])
    unifyCon environment recordType (at (TRecord (at (CConcat first rest))))
    requireDisjoint environment first rest location
    pure (at (ECut record' name' field rest), at (TRecord rest))
  S.SECutMulti record fields -> do
    (record', recordType) <- inferExpression environment record
    fields' <- withEnvironment environment (checkCon fields (at (KRecord (at KType))))
    rest <- freshConMeta location 0 (at (KRecord (at KType))) "cut-rest"
    unifyCon environment recordType (at (TRecord (at (CConcat fields' rest))))
    requireDisjoint environment fields' rest location
    pure (at (ECutMulti record' fields' rest), at (TRecord rest))
  S.SEWild -> do
    typ <- freshConMeta location 0 (at KType) "wild-expression"
    expression <- freshExprMeta location
    case locatedValue expression of
      EMeta identifier -> addConstraint (ClassConstraint environment typ identifier location)
      _ -> pure ()
    pure (expression, typ)
  S.SECase scrutinee branches -> do
    (scrutinee', scrutineeType) <- inferExpression environment scrutinee
    result <- freshConMeta location 0 (at KType) "case-result"
    branches' <- forM branches $ \(patternSource, branch) -> do
      (pattern', branchEnvironment) <- checkPattern environment patternSource scrutineeType
      (branch', branchType) <- inferExpression branchEnvironment branch
      unifyCon branchEnvironment branchType result
      pure (pattern', branch')
    checkPatternExhaustiveness environment location scrutineeType (map fst branches')
    pure (at (ECase scrutinee' branches' scrutineeType result), result)
  S.SELet declarations body -> do
    (declarations', bodyEnvironment) <- elaborateLocalDeclarations environment declarations
    (body', bodyType) <- inferExpression bodyEnvironment body
    pure (at (ELet declarations' body' bodyType), bodyType)
  where
    location = S.locatedSpan source
    at = Located location

elaborateHead :: Environment -> Inference -> Expr -> Con -> ElabM (Expr, Con)
elaborateHead environment inference = if inference == DontInfer then kindOnly else unravel
  where
    kindOnly expression typ = do
      typ' <- headNormalizeCon environment typ
      case locatedValue typ' of
        TKFun _ body -> do
          kind <- freshKindMeta (locatedSpan expression) "kind-argument"
          kindOnly (Located (locatedSpan expression) (EKApp expression kind)) (substituteKindInCon 0 kind body)
        _ -> pure (expression, typ')
    unravel expression typ = do
      typ' <- headNormalizeCon environment typ
      case locatedValue typ' of
        TKFun _ body -> do
          kind <- freshKindMeta (locatedSpan expression) "kind-argument"
          unravel (Located (locatedSpan expression) (EKApp expression kind)) (substituteKindInCon 0 kind body)
        TCFun Implicit name kind body -> do
          argument <- freshConMeta (locatedSpan expression) 0 kind name
          unravel (Located (locatedSpan expression) (ECApp expression argument)) (substituteCon 0 argument body)
        TFun domain range
          | inference /= TypesOnly
          , isClassLike environment domain -> do
              dictionary <- freshExprMeta (locatedSpan expression)
              case locatedValue dictionary of
                EMeta identifier -> addConstraint (ClassConstraint environment domain identifier (locatedSpan expression))
                _ -> pure ()
              unravel (Located (locatedSpan expression) (EApp expression dictionary)) range
        TDisjoint left right body
          | inference /= TypesOnly -> requireDisjoint environment left right (locatedSpan expression) >> unravel expression body
        _ -> pure (expression, typ')

isClassLike :: Environment -> Con -> Bool
isClassLike environment constructor = case classHead constructor of
  Just key | Set.member key (environmentClasses environment) -> True
  _ | hasFolderHead constructor -> True
  _ -> case locatedValue constructor of
    TRecord row -> rowHasClass row
    _ -> False
  where
    hasFolderHead current = case locatedValue current of
      CApp function _ -> hasFolderHead function
      CKApp function _ -> hasFolderHead function
      CNamed identifier -> maybe False (maybe False hasFolderHead . conBindingDefinition) (lookupConstructor environment identifier)
      CModProj identifier [] "folder" -> environmentTopId environment == Just identifier
      _ -> False
    rowHasClass row = case locatedValue row of
      CRecord _ fields -> any (isClassLike environment . snd) fields
      CConcat left right -> rowHasClass left || rowHasClass right
      CApp function _ -> case locatedValue function of
        CApp mapper mapping | isMap mapper -> mappingProducesClass mapping
        _ -> False
      _ -> False
    isMap mapper = case locatedValue mapper of
      CMap {} -> True
      CNamed identifier -> maybe False (maybe False isMap . conBindingDefinition) (lookupConstructor environment identifier)
      _ -> False
    mappingProducesClass mapping = case locatedValue mapping of
      CAbs _ _ body -> isClassLike environment body
      _ -> isClassLike environment mapping

lookupValue :: Environment -> [String] -> String -> ElabM (Maybe (Expr, Con))
lookupValue environment modules name = case modules of
  [] -> case lookupRelative name (environmentRelativeValues environment) of
    Just (index, binding) -> pure (Just (Located (locatedSpan (relativeValueType binding)) (ERel index), relativeValueType binding))
    Nothing -> case Map.lookup name (environmentValues environment) of
      Nothing -> pure Nothing
      Just binding -> do
        typ <- zonkCon (valueBindingType binding)
        let depth = length (environmentRelativeConstructors environment)
        pure (Just (valueBindingExpression binding, liftConMetaDepth depth typ))
  _ -> pure $ do
    (root, path, signature) <- resolveStructurePath environment modules
    binding <- projectValue signature name
    let typ = projectConAt root path signature (valueBindingType binding)
    pure (Located (locatedSpan typ) (EModProj root path name), typ)

lookupRelative :: String -> [RelativeValue] -> Maybe (Int, RelativeValue)
lookupRelative target = go 0
  where
    go _ [] = Nothing
    go index (binding : rest)
      | relativeValueName binding == target = Just (index, binding)
      | otherwise = go (index + 1) rest

findInference :: S.SExpr -> Maybe Inference
findInference source = case locatedValue source of
  S.SEVar _ _ inference -> Just inference
  S.SEApp function _ -> findInference function
  S.SECApp function _ -> findInference function
  _ -> Nothing

requireFieldDisjointness :: Environment -> Span -> Kind -> [(Con, Con)] -> ElabM ()
requireFieldDisjointness environment at element = go
  where
    go [] = pure ()
    go (field : rest) = do
      let singleton (name, value) = Located at (CRecord element [(name, value)])
      mapM_ (\other -> requireDisjoint environment (singleton field) (singleton other) at) rest
      go rest

elaborateLocalDeclarations :: Environment -> [S.SEDecl] -> ElabM ([EDecl], Environment)
elaborateLocalDeclarations = go []
  where
    go done environment [] = pure (done, environment)
    go done environment (source : rest) = case locatedValue source of
      S.SEDVal patternSource expression -> do
        (expression', expressionType) <- inferExpression environment expression
        (pattern', environment') <- checkPattern environment patternSource expressionType
        settleDelayedRows
        checkPatternExhaustiveness environment (locatedSpan patternSource) expressionType [pattern']
        go (done <> [Located (locatedSpan source) (EDVal pattern' expressionType expression')]) environment' rest
      S.SEDValRec bindings -> do
        prepared <- forM bindings $ \(name, annotation, expression) -> do
          typ <- maybe (freshConMeta (locatedSpan source) 0 (Located (locatedSpan source) KType) name) (\sourceType -> withEnvironment environment (checkCon sourceType (Located (locatedSpan source) KType))) annotation
          pure (name, typ, expression)
        let recursiveEnvironment = foldl (\current (name, typ, _) -> bindRelativeValue name typ current) environment prepared
        bindings' <- forM prepared $ \(name, typ, expression) -> do
          (expression', actualType) <- inferExpression recursiveEnvironment expression
          unifyCon recursiveEnvironment actualType typ
          unless (allowableRecursive expression) (withSpanError "illegal-recursion" (S.locatedSpan expression) ("Recursive value " <> name <> " is not a function"))
          pure (name, typ, expression')
        settleDelayedRows
        go (done <> [Located (locatedSpan source) (EDValRec bindings')]) recursiveEnvironment rest

allowableRecursive :: S.SExpr -> Bool
allowableRecursive source = case locatedValue source of
  S.SEAbs {} -> True
  S.SECAbs _ _ _ body -> allowableRecursive body
  S.SEKAbs _ body -> allowableRecursive body
  S.SEDisjoint _ _ body -> allowableRecursive body
  _ -> False

checkPatternExhaustiveness :: Environment -> Span -> Con -> [Pattern] -> ElabM ()
checkPatternExhaustiveness environment at _ patterns =
  unless (coversMatrix [[pattern'] | pattern' <- patterns]) $
    withSpanError "inexhaustive-pattern" at "Pattern match is not exhaustive"
  where
    coversMatrix rows
      | any null rows = True
      | null rows = False
      | Just fields <- firstRecord rows =
          coversMatrix (concatMap (specializeRecord fields) rows)
      | Just universe <- firstConstructorUniverse rows =
          all (\(constructor, hasArgument) -> coversMatrix (concatMap (specializeConstructor constructor hasArgument) rows)) universe
      | otherwise = coversMatrix [rest | pattern' : rest <- rows, isWildcard pattern']

    firstRecord [] = Nothing
    firstRecord ((pattern' : _) : rows) = case locatedValue pattern' of
      PRecord fields _ -> Just [name | (name, _, _) <- fields]
      _ -> firstRecord rows
    firstRecord (_ : rows) = firstRecord rows

    specializeRecord names (pattern' : rest) = case locatedValue pattern' of
      PVar {} -> [replicate (length names) wildcard <> rest]
      PRecord fields flexible ->
        let fieldMap = Map.fromList [(name, fieldPattern) | (name, fieldPattern, _) <- fields]
            nested = map (\name -> Map.findWithDefault wildcard name fieldMap) names
         in if flexible || all (`Map.member` fieldMap) names
              then [nested <> rest]
              else []
      _ -> []
    specializeRecord _ [] = []

    firstConstructorUniverse [] = Nothing
    firstConstructorUniverse ((pattern' : _) : rows) = case locatedValue pattern' of
      PCon _ constructor _ _ -> constructorUniverse constructor <|> firstConstructorUniverse rows
      _ -> firstConstructorUniverse rows
    firstConstructorUniverse (_ : rows) = firstConstructorUniverse rows

    constructorUniverse constructor = do
      chosen <- constructorBinding constructor
      datatype <- case constructor of
        PConVar _ -> Map.lookup (dataConstructorDatatype chosen) (environmentDatatypes environment)
        PConProj root path name -> projectedDatatype root path name
      pure
        [ (constructorNameLike constructor name binding, maybe False (const True) (dataConstructorArgument binding))
        | (name, binding) <- datatypeBindingConstructors datatype
        ]
    constructorBinding constructor = case constructor of
      PConVar identifier -> firstJust
        [if dataConstructorId binding == identifier then Just binding else Nothing | binding <- Map.elems (environmentDataConstructors environment)]
      PConProj root path name -> do
        signature <- projectedSignature root path
        projectDataConstructor signature name
    projectedDatatype root path name = projectedSignature root path >>= (`projectDatatypeForConstructor` name)
    projectedSignature root path = do
      binding <- Map.lookup root (environmentStructuresById environment)
      descendSignatureForPattern (structureBindingSignature binding) path
    descendSignatureForPattern signature [] = Just (headNormalizeSignature environment signature)
    descendSignatureForPattern signature (name : rest) = do
      (_, nested) <- projectStructure (headNormalizeSignature environment signature) name
      descendSignatureForPattern nested rest
    constructorNameLike original name binding = case original of
      PConVar _ -> PConVar (dataConstructorId binding)
      PConProj root path _ -> PConProj root path name

    specializeConstructor expected hasArgument (pattern' : rest) = case locatedValue pattern' of
      PVar {} -> [(if hasArgument then [wildcard] else []) <> rest]
      PCon _ actual _ argument | constructorEquivalent actual expected ->
        [(if hasArgument then [maybe wildcard id argument] else []) <> rest]
      _ -> []
    specializeConstructor _ _ [] = []

    isWildcard pattern' = case locatedValue pattern' of
      PVar {} -> True
      _ -> False
    wildcard = Located at (PVar "_" (Located at CError))
    firstJust [] = Nothing
    firstJust (candidate : rest) = candidate <|> firstJust rest
    constructorEquivalent left right = constructorName left == constructorName right
    constructorName constructor = case constructor of
      PConProj _ _ name -> Just name
      PConVar identifier -> fst <$> listToMaybe
        [(name, binding) | (name, binding) <- Map.toList (environmentDataConstructors environment), dataConstructorId binding == identifier]
