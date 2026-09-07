-- | Small orchestration helpers shared by signature, expression, declaration,
-- and structure elaboration.  This module owns temporary environment scope and
-- the few Basis constructors used across those judgments.
module Vr.Elaborate.Context
  ( withEnvironment
  , inferConIn
  , qualify
  , basisApplied
  , settleDelayedRows
  ) where

import Control.Monad (when)
import qualified Data.Map.Strict as Map
import Vr.Elaborate.Records (retryDelayedRows)
import Vr.Elaborate.State
import Vr.Elaborate.Types
import qualified Vr.Source as S
import Vr.Source (Located (..), Span)

withEnvironment :: Environment -> ElabM value -> ElabM value
withEnvironment environment action = do
  previous <- getEnvironment
  putEnvironment environment
  value <- action
  putEnvironment previous
  pure value

inferConIn :: Environment -> S.SCon -> ElabM (Con, Kind)
inferConIn environment source = withEnvironment environment (inferCon source)

qualify :: [String] -> String -> String
qualify modules name = foldr (\piece suffix -> piece <> "." <> suffix) name modules

basisApplied :: Environment -> Span -> String -> [Con] -> Con
basisApplied environment at name arguments = foldl apply headCon arguments
  where
    apply function argument = Located at (CApp function argument)
    headCon = case Map.lookup "Basis" (environmentStructures environment) of
      Just binding -> Located at (CModProj (structureBindingId binding) [] name)
      Nothing -> maybe (Located at CError) (Located at . CNamed . conBindingId) (Map.lookup name (environmentConstructors environment))

settleDelayedRows :: ElabM ()
settleDelayedRows = do
  solved <- retryDelayedRows False
  when (solved > 0) settleDelayedRows
