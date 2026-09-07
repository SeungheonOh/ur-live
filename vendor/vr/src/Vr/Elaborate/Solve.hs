-- | Fixed-point scheduling for row, disjointness, and instance obligations.
module Vr.Elaborate.Solve
  ( solveAllConstraints
  ) where

import Control.Monad.State.Strict (gets)
import qualified Data.IntMap.Strict as IntMap
import Vr.Elaborate.Classes
import Vr.Elaborate.Disjoint
import Vr.Elaborate.Records
import Vr.Elaborate.State

solveAllConstraints :: ElabM ()
solveAllConstraints = loop
  where
    loop = do
      before <- gets progressSnapshot
      rowsSolved <- retryDelayedRows False
      constraints <- takeConstraints
      outcomes <- mapM solveOne constraints
      let pending = [constraint | (constraint, False) <- zip constraints outcomes]
          solved = length (filter id outcomes) + rowsSolved
      mapM_ addConstraint pending
      after <- gets progressSnapshot
      if solved > 0 && progressed before after
        then loop
        else do
          _ <- retryDelayedRows True
          remaining <- takeConstraints
          mapM_ (solveFinal >=> ignore) remaining
    solveOne constraint = case constraint of
      DisjointConstraint {} -> solveDisjointConstraint False constraint
      ClassConstraint {} -> solveClassConstraint False constraint
    solveFinal constraint = case constraint of
      DisjointConstraint {} -> solveDisjointConstraint True constraint
      ClassConstraint {} -> solveClassConstraint True constraint
    ignore _ = pure ()
    (>=>) first second value = first value >>= second
    progressSnapshot state =
      ( elaborationNextMeta state
      , elaborationKindSolutions state
      , elaborationConSolutions state
      , elaborationExprSolutions state
      , length (elaborationConstraints state)
      , length (elaborationDelayedRows state)
      )
    progressed (limit, oldKinds, oldCons, oldExprs, oldConstraints, oldRows)
               (_, newKinds, newCons, newExprs, newConstraints, newRows) =
      gainedOldSolution limit oldKinds newKinds
        || gainedOldSolution limit oldCons newCons
        || gainedOldSolution limit oldExprs newExprs
        || newConstraints < oldConstraints
        || newRows < oldRows
    gainedOldSolution limit old new = any
      (\identifier -> identifier < limit && IntMap.notMember identifier old)
      (IntMap.keys new)
