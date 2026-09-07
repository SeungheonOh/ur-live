-- | Reference-compatible Core middle-end sequence through specialization.
module Vr.Core.Optimize
  ( optimizeFile
  , optimizeFileWithSettings
  ) where

import qualified Vr.Core.DatatypeSpecialize as DatatypeSpecialize
import qualified Vr.Core.ExpressionSpecialize as ExpressionSpecialize
import qualified Vr.Core.Reduce as Reduce
import qualified Vr.Core.Rpcify as Rpcify
import qualified Vr.Core.Semantics as Semantics
import qualified Vr.Core.Shake as Shake
import qualified Vr.Core.Specialize as Specialize
import qualified Vr.Core.Syntax as C
import qualified Vr.Core.Tag as Tag
import qualified Vr.Core.Untangle as Untangle
import Vr.Source (Diagnostic)

optimizeFile :: Reduce.ReduceSettings -> C.File -> Either [Diagnostic] C.File
optimizeFile settings = optimizeFileWithSettings settings Semantics.defaultSemanticSettings

optimizeFileWithSettings
  :: Reduce.ReduceSettings
  -> Semantics.SemanticSettings
  -> C.File
  -> Either [Diagnostic] C.File
optimizeFileWithSettings settings semanticSettings core = do
  let untangled = Untangle.untangleFile core
      liveBeforeReduction = Shake.shakeFile untangled
  withRpc <- Rpcify.rpcifyFile liveBeforeReduction
  tagged <- Tag.tagFile (Shake.shakeFile (Untangle.untangleFile withRpc))
  let reduced = Reduce.reduceFile settings (Shake.shakeFile tagged)
      liveBeforeSpecialization = Shake.shakeFile reduced
  valuesSpecialized1 <- Specialize.specializeFile liveBeforeSpecialization
  let datatypesSpecialized1 = DatatypeSpecialize.specializeFile valuesSpecialized1
      liveAfterDatatypes1 = Shake.shakeFile datatypesSpecialized1
      expressionsSpecialized1 = ExpressionSpecialize.specializeFile settings liveAfterDatatypes1
      liveAfterExpressions1 = Shake.shakeFile expressionsSpecialized1
  -- ESpecialize can expose fresh closed constructor applications in generated
  -- bodies.  Ur/Web consequently repeats Unpoly and datatype specialization,
  -- then performs one more expression-specialization fixed point before its
  -- final Core reduction.
  valuesSpecialized2 <- Specialize.specializeFile liveAfterExpressions1
  let datatypesSpecialized2 = DatatypeSpecialize.specializeFile valuesSpecialized2
      liveAfterDatatypes2 = Shake.shakeFile datatypesSpecialized2
      expressionsSpecialized2 = ExpressionSpecialize.specializeFile settings liveAfterDatatypes2
      datatypesSpecialized3 = DatatypeSpecialize.specializeFile expressionsSpecialized2
  Semantics.checkAndEffectize semanticSettings
    (Shake.shakeFile (Reduce.reduceFile settings datatypesSpecialized3))
