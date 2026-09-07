-- | Public Explicit-phase façade.
module Vr.Explicit
  ( explicitFile
  ) where

import qualified Vr.Elaborate.Syntax
import Vr.Explicit.Convert (convertFile)
import qualified Vr.Explicit.Syntax
import Vr.Explicit.Unnest (unnestFile)
import Vr.Source (Diagnostic)

-- | Lift local recursion and erase checking-only evidence from a fully solved
-- elaboration result.
explicitFile :: Vr.Elaborate.Syntax.File -> Either [Diagnostic] Vr.Explicit.Syntax.File
explicitFile = convertFile . unnestFile
