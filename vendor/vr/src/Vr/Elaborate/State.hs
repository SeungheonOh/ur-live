{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Vr.Elaborate.State
  ( ElabM
  , ElabState (..)
  , Environment (..)
  , insertConBinding
  , insertSignatureBinding
  , insertStructureBinding
  , emptyEnvironment
  , initialElabState
  , runElabM
  , report
  , withSpanError
  , freshGlobal
  , freshMeta
  , freshKindMeta
  , freshTupleKindMeta
  , freshConMeta
  , freshExprMeta
  , readKindMeta
  , writeKindMeta
  , readConMeta
  , writeConMeta
  , readExprMeta
  , writeExprMeta
  , getEnvironment
  , putEnvironment
  , modifyEnvironment
  , scopedEnvironment
  , KindBinding (..)
  , ConBinding (..)
  , ValueBinding (..)
  , DataConstructorBinding (..)
  , DatatypeBinding (..)
  , SignatureBinding (..)
  , StructureBinding (..)
  , ProjectionIndex (..)
  , RelativeCon (..)
  , RelativeValue (..)
  , ClassKey (..)
  , InstanceRule (..)
  , DisjointAtom (..)
  , Constraint (..)
  , DelayedRow (..)
  , addConstraint
  , takeConstraints
  , addDelayedRow
  , takeDelayedRows
  ) where

import Control.Monad.State.Strict (MonadState, State, gets, modify', runState)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Vr.Elaborate.Syntax
import Vr.Source
  ( Diagnostic
  , DiagnosticPhase (ElaboratePhase)
  , Located (..)
  , Span
  , diagnostic
  )

data KindBinding = KindBinding
  { kindBindingId :: !GlobalId
  , kindBindingKind :: !Kind
  }
  deriving stock (Eq, Ord, Show)

data ConBinding = ConBinding
  { conBindingId :: !GlobalId
  , conBindingKind :: !Kind
  , conBindingDefinition :: !(Maybe Con)
  , conBindingClass :: !Bool
  }
  deriving stock (Eq, Ord, Show)

data ValueBinding = ValueBinding
  { valueBindingId :: !GlobalId
  , valueBindingType :: !Con
  , valueBindingExpression :: !Expr
  }
  deriving stock (Eq, Ord, Show)

data DataConstructorBinding = DataConstructorBinding
  { dataConstructorKind :: !DatatypeKind
  , dataConstructorId :: !GlobalId
  , dataConstructorDatatype :: !GlobalId
  , dataConstructorParameters :: ![String]
  , dataConstructorArgument :: !(Maybe Con)
  , dataConstructorType :: !Con
  }
  deriving stock (Eq, Ord, Show)

data DatatypeBinding = DatatypeBinding
  { datatypeBindingId :: !GlobalId
  , datatypeBindingParameters :: ![String]
  , datatypeBindingConstructors :: ![(String, DataConstructorBinding)]
  }
  deriving stock (Eq, Ord, Show)

data SignatureBinding = SignatureBinding
  { signatureBindingId :: !GlobalId
  , signatureBindingSignature :: !Signature
  }
  deriving stock (Eq, Ord, Show)

data StructureBinding = StructureBinding
  { structureBindingId :: !GlobalId
  , structureBindingSignature :: !Signature
  }
  deriving stock (Eq, Ord, Show)

data RelativeCon = RelativeCon
  { relativeConName :: !String
  , relativeConKind :: !Kind
  }
  deriving stock (Eq, Ord, Show)

data RelativeValue = RelativeValue
  { relativeValueName :: !String
  , relativeValueType :: !Con
  }
  deriving stock (Eq, Ord, Show)

data ClassKey
  = ClassNamed !GlobalId
  | ClassProjected !GlobalId ![String] !String
  deriving stock (Eq, Ord, Show)

data InstanceRule = InstanceRule
  { instanceQuantified :: ![(String, Kind)]
  , instanceHypotheses :: ![Con]
  , instanceConclusion :: !Con
  , instanceDictionary :: !Expr
  }
  deriving stock (Eq, Ord, Show)

data DisjointAtom
  = DisjointName !String ![Int]
  | DisjointMeta !MetaId ![Int]
  | DisjointRelativeName !Int ![Int]
  | DisjointNamedName !GlobalId ![Int]
  | DisjointProjectedName !GlobalId ![String] !String ![Int]
  | DisjointRelativeRow !Int ![Int]
  | DisjointNamedRow !GlobalId ![Int]
  | DisjointProjectedRow !GlobalId ![String] !String ![Int]
  deriving stock (Eq, Ord, Show)

data Constraint
  = DisjointConstraint !Environment !Con !Con !Span
  | ClassConstraint !Environment !Con !MetaId !Span
  deriving stock (Eq, Show)

data DelayedRow = DelayedRow
  { delayedRowEnvironment :: !Environment
  , delayedRowKind :: !Kind
  , delayedRowLeft :: !Con
  , delayedRowRight :: !Con
  , delayedRowSpan :: !Span
  }
  deriving stock (Eq, Show)

data Environment = Environment
  { environmentKinds :: !(Map.Map String KindBinding)
  , environmentConstructors :: !(Map.Map String ConBinding)
  , environmentConstructorsById :: !(Map.Map GlobalId ConBinding)
  , environmentValues :: !(Map.Map String ValueBinding)
  , environmentDataConstructors :: !(Map.Map String DataConstructorBinding)
  , environmentDatatypes :: !(Map.Map GlobalId DatatypeBinding)
  , environmentSignatures :: !(Map.Map String SignatureBinding)
  , environmentSignaturesById :: !(Map.Map GlobalId SignatureBinding)
  , environmentStructures :: !(Map.Map String StructureBinding)
  , environmentStructuresById :: !(Map.Map GlobalId StructureBinding)
  , environmentRelativeKinds :: ![String]
  , environmentRelativeConstructors :: ![RelativeCon]
  , environmentRelativeValues :: ![RelativeValue]
  , environmentClasses :: !(Set.Set ClassKey)
  , environmentOpenRules :: !(Map.Map ClassKey [InstanceRule])
  , environmentClosedRules :: !(Map.Map ClassKey [InstanceRule])
  , environmentDisjointFacts :: !(Map.Map DisjointAtom (Set.Set DisjointAtom))
  , environmentTopId :: !(Maybe GlobalId)
  , environmentLessSafeFfi :: !Bool
  }
  deriving stock (Eq, Show)

data ProjectionIndex = ProjectionIndex
  { projectionConstructorPaths :: !(Map.Map GlobalId ([String], String))
  , projectionStructurePaths :: !(Map.Map GlobalId [String])
  , projectionBindings :: !(Map.Map ([String], String) ConBinding)
  }
  deriving stock (Eq, Show)

emptyEnvironment :: Environment
emptyEnvironment =
  Environment
    { environmentKinds = Map.empty
    , environmentConstructors = Map.empty
    , environmentConstructorsById = Map.empty
    , environmentValues = Map.empty
    , environmentDataConstructors = Map.empty
    , environmentDatatypes = Map.empty
    , environmentSignatures = Map.empty
    , environmentSignaturesById = Map.empty
    , environmentStructures = Map.empty
    , environmentStructuresById = Map.empty
    , environmentRelativeKinds = []
    , environmentRelativeConstructors = []
    , environmentRelativeValues = []
    , environmentClasses = Set.empty
    , environmentOpenRules = Map.empty
    , environmentClosedRules = Map.empty
    , environmentDisjointFacts = Map.empty
    , environmentTopId = Nothing
    , environmentLessSafeFfi = False
    }

insertConBinding :: String -> ConBinding -> Environment -> Environment
insertConBinding name binding environment =
  environment
    { environmentConstructors = Map.insert name binding (environmentConstructors environment)
    , environmentConstructorsById = Map.insert (conBindingId binding) binding (environmentConstructorsById environment)
    }

insertSignatureBinding :: String -> SignatureBinding -> Environment -> Environment
insertSignatureBinding name binding environment =
  environment
    { environmentSignatures = Map.insert name binding (environmentSignatures environment)
    , environmentSignaturesById = Map.insert (signatureBindingId binding) binding (environmentSignaturesById environment)
    }

insertStructureBinding :: String -> StructureBinding -> Environment -> Environment
insertStructureBinding name binding environment =
  environment
    { environmentStructures = Map.insert name binding (environmentStructures environment)
    , environmentStructuresById = Map.insert (structureBindingId binding) binding (environmentStructuresById environment)
    }

data ElabState = ElabState
  { elaborationNextGlobal :: !Int
  , elaborationNextMeta :: !Int
  , elaborationKindSolutions :: !(IntMap.IntMap Kind)
  , elaborationConSolutions :: !(IntMap.IntMap Con)
  , elaborationConMetaScopes :: !(IntMap.IntMap Int)
  , elaborationExprSolutions :: !(IntMap.IntMap Expr)
  , elaborationProjectionIndexes :: !(Map.Map GlobalId ProjectionIndex)
  , elaborationEnvironment :: !Environment
  , elaborationConstraints :: ![Constraint]
  , elaborationDelayedRows :: ![DelayedRow]
  , elaborationDiagnosticsRev :: ![Diagnostic]
  }
  deriving stock (Eq, Show)

initialElabState :: Environment -> ElabState
initialElabState environment =
  ElabState
    { elaborationNextGlobal = 0
    , elaborationNextMeta = 0
    , elaborationKindSolutions = IntMap.empty
    , elaborationConSolutions = IntMap.empty
    , elaborationConMetaScopes = IntMap.empty
    , elaborationExprSolutions = IntMap.empty
    , elaborationProjectionIndexes = Map.empty
    , elaborationEnvironment = environment
    , elaborationConstraints = []
    , elaborationDelayedRows = []
    , elaborationDiagnosticsRev = []
    }

newtype ElabM value = ElabM {unElabM :: State ElabState value}
  deriving newtype (Functor, Applicative, Monad, MonadState ElabState)

runElabM :: Environment -> ElabM value -> (Either [Diagnostic] value, ElabState)
runElabM environment action =
  let (value, finalState) = runState (unElabM action) (initialElabState environment)
      problems = reverse (elaborationDiagnosticsRev finalState)
   in (if null problems then Right value else Left problems, finalState)

report :: Diagnostic -> ElabM ()
report problem = modify' (\state -> state {elaborationDiagnosticsRev = problem : elaborationDiagnosticsRev state})

withSpanError :: String -> Span -> String -> ElabM ()
withSpanError code at message = report (diagnostic ElaboratePhase code at message)

freshGlobal :: ElabM GlobalId
freshGlobal = do
  next <- gets elaborationNextGlobal
  modify' (\state -> state {elaborationNextGlobal = next + 1})
  pure (GlobalId next)

freshMeta :: ElabM MetaId
freshMeta = do
  next <- gets elaborationNextMeta
  modify' (\state -> state {elaborationNextMeta = next + 1})
  pure (MetaId next)

freshKindMeta :: Span -> String -> ElabM Kind
freshKindMeta at name = do
  identifier <- freshMeta
  pure (Located at (KMeta identifier at name))

freshTupleKindMeta :: Span -> ElabM Kind
freshTupleKindMeta at = do
  identifier <- freshMeta
  pure (Located at (KTupleMeta identifier at []))

freshConMeta :: Span -> Int -> Kind -> String -> ElabM Con
freshConMeta at depth kind name = do
  identifier <- freshMeta
  scope <- gets elaborationNextGlobal
  modify' (\state -> state {elaborationConMetaScopes = IntMap.insert (unMetaId identifier) scope (elaborationConMetaScopes state)})
  pure (Located at (CMeta identifier depth kind name))

freshExprMeta :: Span -> ElabM Expr
freshExprMeta at = do
  identifier <- freshMeta
  pure (Located at (EMeta identifier))

readKindMeta :: MetaId -> ElabM (Maybe Kind)
readKindMeta identifier = gets (IntMap.lookup (unMetaId identifier) . elaborationKindSolutions)

writeKindMeta :: MetaId -> Kind -> ElabM ()
writeKindMeta identifier kind = modify' (\state -> state {elaborationKindSolutions = IntMap.insert (unMetaId identifier) kind (elaborationKindSolutions state)})

readConMeta :: MetaId -> ElabM (Maybe Con)
readConMeta identifier = gets (IntMap.lookup (unMetaId identifier) . elaborationConSolutions)

writeConMeta :: MetaId -> Con -> ElabM ()
writeConMeta identifier constructor = modify' (\state -> state {elaborationConSolutions = IntMap.insert (unMetaId identifier) constructor (elaborationConSolutions state)})

readExprMeta :: MetaId -> ElabM (Maybe Expr)
readExprMeta identifier = gets (IntMap.lookup (unMetaId identifier) . elaborationExprSolutions)

writeExprMeta :: MetaId -> Expr -> ElabM ()
writeExprMeta identifier expression = modify' (\state -> state {elaborationExprSolutions = IntMap.insert (unMetaId identifier) expression (elaborationExprSolutions state)})

getEnvironment :: ElabM Environment
getEnvironment = gets elaborationEnvironment

putEnvironment :: Environment -> ElabM ()
putEnvironment environment = modify' (\state -> state {elaborationEnvironment = environment})

modifyEnvironment :: (Environment -> Environment) -> ElabM ()
modifyEnvironment change = modify' (\state -> state {elaborationEnvironment = change (elaborationEnvironment state)})

scopedEnvironment :: ElabM value -> ElabM value
scopedEnvironment action = do
  before <- getEnvironment
  value <- action
  putEnvironment before
  pure value

addConstraint :: Constraint -> ElabM ()
addConstraint constraint = modify' (\state -> state
  { elaborationConstraints = constraint : elaborationConstraints state
  })

takeConstraints :: ElabM [Constraint]
takeConstraints = do
  constraints <- gets elaborationConstraints
  modify' (\state -> state {elaborationConstraints = []})
  pure (reverse constraints)

addDelayedRow :: DelayedRow -> ElabM ()
addDelayedRow delayed = modify' (\state -> state
  { elaborationDelayedRows = delayed : elaborationDelayedRows state
  })

takeDelayedRows :: ElabM [DelayedRow]
takeDelayedRows = do
  delayed <- gets elaborationDelayedRows
  modify' (\state -> state {elaborationDelayedRows = []})
  pure (reverse delayed)
