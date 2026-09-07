{-# LANGUAGE DerivingStrategies #-}

-- | Ordered type-class rule extraction and dictionary search.  Open rules
-- (relative assumptions) precede closed rules (named values), matching the
-- reference compiler's shadowing behavior.
module Vr.Elaborate.Classes
  ( Resolution (..)
  , classHead
  , registerClass
  , bindNamedValue
  , bindInstanceValue
  , bindRelativeValue
  , resolveClass
  , solveClassConstraint
  ) where

import Control.Monad.State.Strict (get, put)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Vr.Elaborate.Records (summarizeRow, RowSummary (..))
import Vr.Elaborate.State
import Vr.Elaborate.Types
import Vr.Source (Located (..))

data Resolution = Resolved !Expr | ResolutionDelayed | NoResolution
  deriving stock (Eq, Show)

classHead :: Con -> Maybe ClassKey
classHead constructor = case locatedValue constructor of
  CApp function _ -> classHead function
  CAbs _ _ body -> classHead body
  CNamed identifier -> Just (ClassNamed identifier)
  CModProj identifier path name -> Just (ClassProjected identifier path name)
  _ -> Nothing

registerClass :: String -> GlobalId -> Kind -> Maybe Con -> Environment -> Environment
registerClass name identifier kind definition environment =
  (insertConBinding name (ConBinding identifier kind definition True) environment)
    { environmentClasses = Set.insert key (environmentClasses environment)
    , environmentOpenRules = Map.insertWith (<>) key [] (environmentOpenRules environment)
    , environmentClosedRules = Map.insertWith (<>) key [] (environmentClosedRules environment)
    }
  where key = ClassNamed identifier

bindNamedValue :: String -> GlobalId -> Con -> Expr -> Environment -> Environment
bindNamedValue name identifier typ expression environment =
  addRule False typ expression environment
    { environmentValues = Map.insert name (ValueBinding identifier typ expression) (environmentValues environment)
    }

-- | Register a qualified value as a possible instance without bringing its
-- unqualified name into scope.
bindInstanceValue :: Con -> Expr -> Environment -> Environment
bindInstanceValue = addRule False

bindRelativeValue :: String -> Con -> Environment -> Environment
bindRelativeValue name typ environment =
  addRule True typ (Located (locatedSpan typ) (ERel 0)) shifted
    { environmentRelativeValues = RelativeValue name typ : environmentRelativeValues shifted
    }
  where
    shifted = environment {environmentOpenRules = fmap (map liftRule) (environmentOpenRules environment)}
    liftRule rule = rule {instanceDictionary = liftExpr 0 1 (instanceDictionary rule)}

addRule :: Bool -> Con -> Expr -> Environment -> Environment
addRule open typ expression environment = case recognizeRule environment typ expression of
  Nothing -> environment
  Just (key, rule) ->
    if open
      then environment {environmentOpenRules = Map.insertWith (<>) key [rule] (environmentOpenRules environment)}
      else environment {environmentClosedRules = Map.insertWith (<>) key [rule] (environmentClosedRules environment)}

recognizeRule :: Environment -> Con -> Expr -> Maybe (ClassKey, InstanceRule)
recognizeRule environment typ expression = do
  let (quantified, body) = quantifiers [] typ
      (hypotheses, conclusion) = clauses [] body
  rawKey <- classHead conclusion
  let key = canonicalClassKey environment rawKey
  if Set.member rawKey (environmentClasses environment) || Set.member key (environmentClasses environment)
    then Just (key, InstanceRule quantified hypotheses conclusion expression)
    else Nothing
  where
    quantifiers acc constructor = case locatedValue constructor of
      TCFun _ name kind body -> quantifiers (acc <> [(name, kind)]) body
      _ -> (acc, constructor)
    clauses acc constructor = case locatedValue constructor of
      TFun hypothesis body
        | Just key <- classHead hypothesis
        , Set.member key (environmentClasses environment) -> clauses (acc <> [hypothesis]) body
      _ -> (acc, constructor)

canonicalClassKey :: Environment -> ClassKey -> ClassKey
canonicalClassKey environment key = case key of
  ClassNamed identifier -> case lookupConstructor environment identifier >>= conBindingDefinition >>= classHead of
    Just projected -> projected
    Nothing -> key
  _ -> key

resolveClass :: Environment -> Con -> ElabM Resolution
resolveClass environment goal0 = do
  goal <- headNormalizeCon environment goal0
  if startsWithUnknown goal
    then pure ResolutionDelayed
    else case locatedValue goal of
      TRecord row -> resolveRecord environment goal row
      _ -> case classHead goal of
        Nothing -> folderFallback environment goal0
        Just key -> tryRules (Map.findWithDefault [] key (environmentOpenRules environment) <> Map.findWithDefault [] key (environmentClosedRules environment))
  where
    tryRules [] = folderFallback environment goal0
    tryRules (rule : rest) = do
      before <- get
      attempted <- tryRule environment goal0 rule
      case attempted of
        Resolved expression -> pure (Resolved expression)
        _ -> put before >> tryRules rest

solveClassConstraint :: Bool -> Constraint -> ElabM Bool
solveClassConstraint final constraint = case constraint of
  ClassConstraint environment goal target at -> do
    resolution <- resolveClass environment goal
    case resolution of
      Resolved expression -> writeExprMeta target expression >> pure True
      ResolutionDelayed | not final -> pure False
      _ | not final -> pure False
      ResolutionDelayed -> withSpanError "unresolved-class" at ("Type-class goal is still ambiguous: " <> show goal) >> pure True
      NoResolution -> do
        normalized <- headNormalizeCon environment goal
        withSpanError "unresolvable-class" at ("No instance resolves " <> show normalized)
        pure True
  _ -> pure False

tryRule :: Environment -> Con -> InstanceRule -> ElabM Resolution
tryRule environment goal rule = do
  metas <- mapM (\(name, kind) -> freshConMeta (locatedSpan goal) 0 kind name) (instanceQuantified rule)
  let instantiate = instantiateQuantified metas
      conclusion = instantiate (instanceConclusion rule)
      hypotheses = map instantiate (instanceHypotheses rule)
  before <- get
  unifyCon environment goal conclusion
  after <- get
  if length (elaborationDiagnosticsRev before) /= length (elaborationDiagnosticsRev after)
    then put before >> pure NoResolution
    else do
      evidence <- resolveHypotheses hypotheses
      case evidence of
        Nothing -> put before >> pure NoResolution
        Just dictionaries -> do
          expression <- applyEvidence (instanceDictionary rule) metas dictionaries
          pure (Resolved expression)
  where
    resolveHypotheses [] = pure (Just [])
    resolveHypotheses (hypothesis : rest) = do
      result <- resolveClass environment hypothesis
      case result of
        Resolved dictionary -> fmap (dictionary :) <$> resolveHypotheses rest
        _ -> pure Nothing
    applyEvidence expression metas dictionaries = do
      metas' <- mapM zonkCon metas
      let withTypes = foldl (\function argument -> Located (locatedSpan goal) (ECApp function argument)) expression metas'
      pure (foldl (\function argument -> Located (locatedSpan goal) (EApp function argument)) withTypes dictionaries)

instantiateQuantified :: [Con] -> Con -> Con
instantiateQuantified metas constructor = foldl apply constructor (zip [length metas - 1, length metas - 2 .. 0] metas)
  where apply body (depth, replacement) = substituteCon depth replacement body

resolveRecord :: Environment -> Con -> Con -> ElabM Resolution
resolveRecord environment goal row = do
  summary <- summarizeRow environment row
  if null (rowMetas summary) && null (rowOthers summary)
    then do
      fields <- resolveFields (rowFields summary)
      pure $ maybe NoResolution (Resolved . Located (locatedSpan goal) . ERecord) fields
    else pure ResolutionDelayed
  where
    resolveFields [] = pure (Just [])
    resolveFields ((name, typ) : rest) = do
      resolution <- resolveClass environment typ
      case resolution of
        Resolved dictionary -> fmap ((name, dictionary, typ) :) <$> resolveFields rest
        _ -> pure Nothing

folderFallback :: Environment -> Con -> ElabM Resolution
folderFallback environment goal0 = do
  goal <- headNormalizeCon environment goal0
  case locatedValue goal of
    CApp function row -> do
      function' <- headNormalizeCon environment function
      case locatedValue function' of
        CKApp folder element
          | isFolder folder -> do
              summary <- summarizeRow environment row
              if null (rowMetas summary) && null (rowOthers summary)
                then pure (Resolved (buildFolder element (rowFields summary)))
                else pure ResolutionDelayed
        _ -> pure NoResolution
    _ -> pure NoResolution
  where
    isFolder constructor = case locatedValue constructor of
      CModProj identifier [] "folder" -> environmentTopId environment == Just identifier
      _ -> False
    buildFolder element fields = fst (foldr (cons element) (nil element, []) fields)
    nil element = Located (locatedSpan goal0) (EKApp (topValue ["Folder"] "nil") element)
    cons element (name, value) (folder, rest) =
      let start = Located at (EKApp (topValue ["Folder"] "cons") element)
          withRest = Located at (ECApp start (Located at (CRecord element rest)))
          withName = Located at (ECApp withRest name)
          withValue = Located at (ECApp withName value)
       in (Located at (EApp withValue folder), (name, value) : rest)
    topValue path name = case environmentTopId environment of
      Just identifier -> Located at (EModProj identifier path name)
      Nothing -> Located at EError
    at = locatedSpan goal0

startsWithUnknown :: Con -> Bool
startsWithUnknown constructor = case firstArgument constructor of
  Nothing -> False
  Just argument -> hasMeta argument
  where
    firstArgument current = case locatedValue current of
      CApp function argument -> case firstArgument function of
        Nothing -> Just argument
        result -> result
      _ -> Nothing
    hasMeta current = case locatedValue current of
      CMeta {} -> True
      CApp left right -> hasMeta left || hasMeta right
      CRecord _ fields -> any (\(name, value) -> hasMeta name || hasMeta value) fields
      CConcat left right -> hasMeta left || hasMeta right
      CProj tuple _ -> hasMeta tuple
      _ -> False

liftExpr :: Int -> Int -> Expr -> Expr
liftExpr cutoff amount expression = expression {locatedValue = case locatedValue expression of
  ERel index | index >= cutoff -> ERel (index + amount)
  EApp function argument -> EApp (go function) (go argument)
  EAbs name domain range body -> EAbs name domain range (liftExpr (cutoff + 1) amount body)
  ECApp function argument -> ECApp (go function) argument
  ECAbs explicitness name kind body -> ECAbs explicitness name kind (go body)
  EKAbs name body -> EKAbs name (go body)
  EKApp function kind -> EKApp (go function) kind
  ERecord fields -> ERecord [(name, go value, typ) | (name, value, typ) <- fields]
  EField record name field rest -> EField (go record) name field rest
  EConcat left leftType right rightType -> EConcat (go left) leftType (go right) rightType
  ECut record name field rest -> ECut (go record) name field rest
  ECutMulti record fields rest -> ECutMulti (go record) fields rest
  ECase scrutinee branches disc result -> ECase (go scrutinee) [(pattern, go body) | (pattern, body) <- branches] disc result
  ELet declarations body typ -> ELet (map liftDeclaration declarations) (go body) typ
  other -> other}
  where
    go = liftExpr cutoff amount
    liftDeclaration declaration = declaration {locatedValue = case locatedValue declaration of
      EDVal pattern typ value -> EDVal pattern typ (go value)
      EDValRec bindings -> EDValRec [(name, typ, go value) | (name, typ, value) <- bindings]}
