{-# LANGUAGE DerivingStrategies #-}

-- | Ordered row summaries and the retryable row-equation solver.  Rows are
-- never sorted: cancellation follows source order, as in Ur/Web.
module Vr.Elaborate.Records
  ( RowSummary (..)
  , summarizeRow
  , summaryCon
  , solveDelayedRow
  , retryDelayedRows
  , lookupRowField
  ) where

import Control.Monad.State.Strict (get, put)
import Vr.Elaborate.State
import Vr.Elaborate.Types
import Vr.Source (Located (..), Span)

data RowSummary = RowSummary
  { rowFields :: ![(Con, Con)]
  , rowMetas :: ![Con]
  , rowOthers :: ![Con]
  }
  deriving stock (Eq, Show)

instance Semigroup RowSummary where
  RowSummary af am ao <> RowSummary bf bm bo = RowSummary (af <> bf) (am <> bm) (ao <> bo)

instance Monoid RowSummary where
  mempty = RowSummary [] [] []

summarizeRow :: Environment -> Con -> ElabM RowSummary
summarizeRow environment constructor0 = do
  constructor <- headNormalizeCon environment constructor0
  case locatedValue constructor of
    CRecord _ fields -> do
      normalized <- mapM (\(name, value) -> (,) <$> headNormalizeCon environment name <*> headNormalizeCon environment value) fields
      pure mempty {rowFields = normalized}
    CConcat left right -> (<>) <$> summarizeRow environment left <*> summarizeRow environment right
    CMeta _ depth _ _ | depth == 0 -> pure mempty {rowMetas = [constructor]}
    _ -> pure mempty {rowOthers = [constructor]}

summaryCon :: Span -> Kind -> RowSummary -> Con
summaryCon at element summary = foldl concatRow known (rowMetas summary <> rowOthers summary)
  where
    known = Located at (CRecord element (rowFields summary))
    concatRow left right
      | isEmpty left = right
      | isEmpty right = left
      | otherwise = Located at (CConcat left right)
    isEmpty constructor = case locatedValue constructor of
      CRecord _ [] -> True
      _ -> False

solveDelayedRow :: Bool -> DelayedRow -> ElabM Bool
solveDelayedRow final delayed = do
  let environment = delayedRowEnvironment delayed
      at = delayedRowSpan delayed
      rowKind = delayedRowKind delayed
      element = case locatedValue rowKind of
        KRecord value -> value
        _ -> Located at KError
  left <- summarizeRow environment (delayedRowLeft delayed)
  right <- summarizeRow environment (delayedRowRight delayed)
  (leftFields, rightFields) <- cancelFields environment (rowFields left) (rowFields right)
  (leftMetas, rightMetas) <- cancelMatching sameMeta (rowMetas left) (rowMetas right)
  (leftOthers, rightOthers) <- cancelConstructors environment (rowOthers left) (rowOthers right)
  let left' = left {rowFields = leftFields, rowMetas = leftMetas, rowOthers = leftOthers}
      right' = right {rowFields = rightFields, rowMetas = rightMetas, rowOthers = rightOthers}
  solved <- solveResidual environment at element left' right'
  if solved
    then pure True
    else if final
      then withSpanError "row-mismatch" at ("Cannot unify record rows " <> show (summaryCon at element left') <> " and " <> show (summaryCon at element right')) >> pure True
      else pure False

retryDelayedRows :: Bool -> ElabM Int
retryDelayedRows final = do
  delayed <- takeDelayedRows
  outcomes <- mapM (\equation -> (equation,) <$> solveDelayedRow final equation) delayed
  mapM_ (addDelayedRow . fst) (filter (not . snd) outcomes)
  pure (length (filter snd outcomes))

lookupRowField :: Environment -> Con -> Con -> ElabM (Maybe (Con, Con))
lookupRowField environment row name = do
  summary <- summarizeRow environment row
  findField (rowFields summary)
  where
    findField [] = pure Nothing
    findField ((fieldName, fieldType) : rest) = do
      equal <- conEqual environment name fieldName
      if equal
        then do
          let element = Located (locatedSpan row) KType
              remainderFields = filter (\(other, _) -> other /= fieldName) (rowFieldsUnsafe row)
          pure (Just (fieldType, Located (locatedSpan row) (CRecord element remainderFields)))
        else findField rest
    -- The caller only relies on the remainder for fully-known rows.  General
    -- rows get a fresh remainder through normal unification in expression
    -- elaboration.
    rowFieldsUnsafe constructor = case locatedValue constructor of
      CRecord _ fields -> fields
      _ -> []

cancelFields :: Environment -> [(Con, Con)] -> [(Con, Con)] -> ElabM ([(Con, Con)], [(Con, Con)])
cancelFields environment = cancelMatching matches
  where
    matches (leftName, leftValue) (rightName, rightValue) = do
      if definitelyDifferent leftName rightName
        then pure False
        else do
          -- A field match is one atomic unification choice.  Trial-unify the
          -- value first (which disambiguates mapped event rows), then its
          -- possibly-polymorphic name.  Roll back *all* metavariable writes
          -- when either half fails; separate 'conEqual' calls used to retain
          -- value solutions from a name candidate that was later rejected.
          before <- get
          unifyCon environment leftValue rightValue
          afterValue <- get
          if diagnosticsChanged before afterValue
            then put before >> pure False
            else do
              unifyCon environment leftName rightName
              afterName <- get
              if diagnosticsChanged before afterName
                then put before >> pure False
                else pure True

    diagnosticsChanged before after =
      length (elaborationDiagnosticsRev before) /= length (elaborationDiagnosticsRev after)

cancelConstructors :: Environment -> [Con] -> [Con] -> ElabM ([Con], [Con])
cancelConstructors environment = cancelMatching matches
  where
    matches left right
      | left == right = pure True
      | containsMeta left && containsMeta right = pure False
      | otherwise = conEqual environment left right

sameMeta :: Con -> Con -> ElabM Bool
sameMeta left right = pure $ case (locatedValue left, locatedValue right) of
  (CMeta leftId leftLevel _ _, CMeta rightId rightLevel _ _) -> leftId == rightId && leftLevel == rightLevel
  _ -> False

containsMeta :: Con -> Bool
containsMeta constructor = case locatedValue constructor of
  CMeta {} -> True
  TFun domain range -> containsMeta domain || containsMeta range
  TCFun _ _ _ body -> containsMeta body
  TRecord row -> containsMeta row
  TDisjoint left right body -> any containsMeta [left, right, body]
  CApp function argument -> containsMeta function || containsMeta argument
  CAbs _ _ body -> containsMeta body
  CKAbs _ body -> containsMeta body
  CKApp function _ -> containsMeta function
  TKFun _ body -> containsMeta body
  CRecord _ fields -> any (\(name, value) -> containsMeta name || containsMeta value) fields
  CConcat left right -> containsMeta left || containsMeta right
  CTuple elements -> any containsMeta elements
  CProj tuple _ -> containsMeta tuple
  _ -> False

cancelMatching :: (left -> right -> ElabM Bool) -> [left] -> [right] -> ElabM ([left], [right])
cancelMatching predicate = go []
  where
    go passed [] rights = pure (reverse passed, rights)
    go passed (left : lefts) rights = do
      found <- removeFirstM (predicate left) rights
      case found of
        Nothing -> go (left : passed) lefts rights
        Just rights' -> go passed lefts rights'

removeFirstM :: (value -> ElabM Bool) -> [value] -> ElabM (Maybe [value])
removeFirstM predicate = go []
  where
    go _ [] = pure Nothing
    go passed (value : rest) = do
      matches <- predicate value
      if matches then pure (Just (reverse passed <> rest)) else go (value : passed) rest

solveResidual :: Environment -> Span -> Kind -> RowSummary -> RowSummary -> ElabM Bool
solveResidual environment at element left right
  | emptySummary left && emptySummary right = pure True
  | null (rowFields left)
  , null (rowOthers left)
  , emptySummary right = do
      let empty = Located at (CRecord element [])
      mapM_ (\meta -> unifyCon environment meta empty) (rowMetas left)
      pure True
  | emptySummary left
  , null (rowFields right)
  , null (rowOthers right) = do
      let empty = Located at (CRecord element [])
      mapM_ (\meta -> unifyCon environment meta empty) (rowMetas right)
      pure True
  | [meta] <- rowMetas left
  , null (rowFields left)
  , null (rowOthers left) = unifyCon environment meta (summaryCon at element right) >> pure True
  | [meta] <- rowMetas right
  , null (rowFields right)
  , null (rowOthers right) = unifyCon environment meta (summaryCon at element left) >> pure True
  | [leftMeta] <- rowMetas left
  , [rightMeta] <- rowMetas right
  , null (rowOthers left)
  , null (rowOthers right)
  , namesDefinitelySeparate (rowFields left) (rowFields right) = do
      common <- freshConMeta at 0 (Located at (KRecord element)) "row-rest"
      let solveLeft = summaryCon at element (RowSummary (rowFields right) [common] [])
          solveRight = summaryCon at element (RowSummary (rowFields left) [common] [])
      unifyCon environment leftMeta solveLeft
      unifyCon environment rightMeta solveRight
      pure True
  | [meta] <- rowOthers left
  , CMeta {} <- locatedValue meta
  , null (rowFields left)
  , null (rowMetas left) = tryUnify environment meta (summaryCon at element right)
  | [meta] <- rowOthers right
  , CMeta {} <- locatedValue meta
  , null (rowFields right)
  , null (rowMetas right) = tryUnify environment meta (summaryCon at element left)
  | [other] <- rowOthers left
  , null (rowFields left)
  , null (rowMetas left) = invertMap environment at element other right
  | [other] <- rowOthers right
  , null (rowFields right)
  , null (rowMetas right) = invertMap environment at element other left
  | otherwise = pure False

tryUnify :: Environment -> Con -> Con -> ElabM Bool
tryUnify environment left right = do
  before <- get
  unifyCon environment left right
  after <- get
  if length (elaborationDiagnosticsRev before) == length (elaborationDiagnosticsRev after)
    then pure True
    else put before >> pure False

emptySummary :: RowSummary -> Bool
emptySummary (RowSummary fields metas others) = null fields && null metas && null others

namesDefinitelySeparate :: [(Con, Con)] -> [(Con, Con)] -> Bool
namesDefinitelySeparate left right = all (\(leftName, _) -> all (definitelyDifferent leftName . fst) right) left

definitelyDifferent :: Con -> Con -> Bool
definitelyDifferent left right = case (locatedValue left, locatedValue right) of
  (CName first, CName second) -> first /= second
  (CName _, CRel _) -> True
  (CRel _, CName _) -> True
  (CRel first, CRel second) -> first /= second
  (CNamed _, CName _) -> True
  (CName _, CNamed _) -> True
  (CModProj {}, CName _) -> True
  (CName _, CModProj {}) -> True
  (CModProj _ _ first, CModProj _ _ second) -> first /= second
  _ -> False

invertMap :: Environment -> Span -> Kind -> Con -> RowSummary -> ElabM Bool
invertMap environment at _ mapped concrete
  | not (null (rowOthers concrete)) = pure False
  | otherwise = case locatedValue mapped of
  CApp outer resultRow -> case locatedValue outer of
    CApp mapper function -> case locatedValue mapper of
      CMap domain range -> do
        inputFields <- mapM (invertField function domain range) (rowFields concrete)
        inputMetas <- mapM (invertMeta mapper function domain) (rowMetas concrete)
        let input = RowSummary inputFields inputMetas []
        unifyCon environment resultRow (summaryCon at domain input)
        pure True
      _ -> pure False
    _ -> pure False
  _ -> pure False
  where
    invertField function domain range (name, result) = do
      domain' <- zonkKind domain
      input <- case locatedValue domain' of
        KUnit -> pure (Located at CUnit)
        _ -> freshConMeta at 0 domain "map-field"
      unifyCon environment result (Located at (CApp function input))
      resultKind <- conKind environment result
      unifyKind at resultKind range
      pure (name, input)
    invertMeta mapper function domain output = do
      input <- freshConMeta at 0 (Located at (KRecord domain)) "map-row"
      let mappedInput = Located at (CApp (Located at (CApp mapper function)) input)
      unifyCon environment output mappedInput
      pure input
