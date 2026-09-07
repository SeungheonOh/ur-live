{-# LANGUAGE DerivingStrategies #-}

-- | Symbol tables used while evaluating the Explicit module language.  Core
-- has no modules, so a structure is represented only by the flattened names
-- that its projections select.
module Vr.Core.Corify.State
  ( ConTarget (..)
  , ValueTarget (..)
  , Flat (..)
  , FunctorBinding (..)
  , CorifyState (..)
  , initialState
  , makeForeign
  , allocate
  , bindCon
  , bindConDefinition
  , markForeignCon
  , bindValue
  , bindConstructor
  , bindConstructorAs
  , bindValueAs
  , bindForeignValue
  , aliasForeignValue
  , bindStructure
  , bindFunctor
  , insertStructure
  , aliasCon
  , aliasValue
  , aliasConstructor
  , aliasStructure
  , aliasFunctor
  , enter
  , leave
  , lookupConId
  , lookupConDefinition
  , lookupForeignCon
  , lookupValueId
  , lookupConstructorId
  , lookupStructureId
  , lookupFunctorId
  , lookupConName
  , lookupValueName
  , lookupConstructorName
  , lookupStructureName
  , lookupFunctorName
  , projectPath
  , scopePath
  , describeFlat
  ) where

import qualified Data.Map.Strict as Map
import Vr.Core.Syntax (Con, GlobalId (..), PatCon (..))
import qualified Vr.Explicit.Syntax as E

data ConTarget = NormalCon !GlobalId | ForeignCon !String
  deriving stock (Eq, Ord, Show)

data ValueTarget = NormalValue !GlobalId | ForeignValue !String !String !Con
  deriving stock (Eq, Ord, Show)

data FunctorBinding = FunctorBinding
  { functorParameterName :: !String
  , functorParameterId :: !E.GlobalId
  , functorBody :: !E.Structure
  }
  deriving stock (Eq, Ord, Show)

data NormalScope = NormalScope
  { normalPath :: ![String]
  , normalConstructors :: !(Map.Map String PatCon)
  , normalCons :: !(Map.Map String GlobalId)
  , normalValues :: !(Map.Map String ValueTarget)
  , normalStructures :: !(Map.Map String Flat)
  , normalFunctors :: !(Map.Map String FunctorBinding)
  }
  deriving stock (Eq, Ord, Show)

data ForeignScope = ForeignScope
  { foreignScopeModule :: !String
  , foreignScopeValues :: !(Map.Map String Con)
  , foreignScopeConstructors :: !(Map.Map String PatCon)
  }
  deriving stock (Eq, Ord, Show)

data Flat = NormalFlat !NormalScope | ForeignFlat !ForeignScope
  deriving stock (Eq, Ord, Show)

data CorifyState = CorifyState
  { stateNextId :: !Int
  , stateBasisId :: !(Maybe E.GlobalId)
  , stateCons :: !(Map.Map E.GlobalId GlobalId)
  , stateConDefinitions :: !(Map.Map E.GlobalId E.Con)
  , stateForeignCons :: !(Map.Map E.GlobalId (String, String))
  , stateValues :: !(Map.Map E.GlobalId ValueTarget)
  , stateConstructors :: !(Map.Map E.GlobalId PatCon)
  , stateStructures :: !(Map.Map E.GlobalId Flat)
  , stateFunctors :: !(Map.Map E.GlobalId FunctorBinding)
  , stateCurrent :: !Flat
  , stateParents :: ![Flat]
  }
  deriving stock (Eq, Ord, Show)

initialState :: Int -> CorifyState
initialState next =
  CorifyState
    { stateNextId = next
    , stateBasisId = Nothing
    , stateCons = Map.empty
    , stateConDefinitions = Map.empty
    , stateForeignCons = Map.empty
    , stateValues = Map.empty
    , stateConstructors = Map.empty
    , stateStructures = Map.empty
    , stateFunctors = Map.empty
    , stateCurrent = emptyNormal []
    , stateParents = []
    }

emptyNormal :: [String] -> Flat
emptyNormal path = NormalFlat (NormalScope path Map.empty Map.empty Map.empty Map.empty Map.empty)

makeForeign :: String -> Map.Map String Con -> Map.Map String PatCon -> Flat
makeForeign moduleName values constructors = ForeignFlat (ForeignScope moduleName values constructors)

allocate :: CorifyState -> (GlobalId, CorifyState)
allocate state =
  let identifier = GlobalId (stateNextId state)
   in (identifier, state {stateNextId = stateNextId state + 1})

bindCon :: String -> E.GlobalId -> CorifyState -> (GlobalId, CorifyState)
bindCon name old state0 =
  let (identifier, state1) = allocate state0
      current = updateNormal state1 $ \scope -> scope {normalCons = Map.insert name identifier (normalCons scope)}
   in (identifier, current {stateCons = Map.insert old identifier (stateCons current)})

bindConDefinition :: E.GlobalId -> E.Con -> CorifyState -> CorifyState
bindConDefinition identifier definition state =
  state {stateConDefinitions = Map.insert identifier definition (stateConDefinitions state)}

markForeignCon :: E.GlobalId -> String -> String -> CorifyState -> CorifyState
markForeignCon identifier moduleName name state =
  state {stateForeignCons = Map.insert identifier (moduleName, name) (stateForeignCons state)}

bindValue :: String -> E.GlobalId -> CorifyState -> (GlobalId, CorifyState)
bindValue name old state0 =
  let (identifier, state1) = allocate state0
   in (identifier, bindValueAs name old identifier state1)

bindValueAs :: String -> E.GlobalId -> GlobalId -> CorifyState -> CorifyState
bindValueAs name old identifier state =
  let target = NormalValue identifier
      current = updateNormal state $ \scope -> scope {normalValues = Map.insert name target (normalValues scope)}
   in current {stateValues = Map.insert old target (stateValues current)}

bindForeignValue :: String -> E.GlobalId -> String -> Con -> CorifyState -> CorifyState
bindForeignValue name old moduleName typ state =
  let target = ForeignValue moduleName name typ
      current = updateNormal state $ \scope -> scope {normalValues = Map.insert name target (normalValues scope)}
   in current {stateValues = Map.insert old target (stateValues current)}

aliasForeignValue :: E.GlobalId -> String -> String -> Con -> CorifyState -> CorifyState
aliasForeignValue old moduleName name typ state =
  state {stateValues = Map.insert old (ForeignValue moduleName name typ) (stateValues state)}

bindConstructor :: String -> E.GlobalId -> CorifyState -> (GlobalId, CorifyState)
bindConstructor name old state0 =
  let (identifier, state1) = allocate state0
      constructor = PConVar identifier
      state2 = bindConstructorAs name old constructor state1
   in (identifier, bindValueAs name old identifier state2)

bindConstructorAs :: String -> E.GlobalId -> PatCon -> CorifyState -> CorifyState
bindConstructorAs name old constructor state =
  let current = updateNormal state $ \scope -> scope {normalConstructors = Map.insert name constructor (normalConstructors scope)}
   in current {stateConstructors = Map.insert old constructor (stateConstructors current)}

bindStructure :: String -> E.GlobalId -> Flat -> CorifyState -> CorifyState
bindStructure name old inner state =
  let current = updateNormal state $ \scope -> scope {normalStructures = Map.insert name inner (normalStructures scope)}
   in current {stateStructures = Map.insert old inner (stateStructures current)}

bindFunctor :: String -> E.GlobalId -> FunctorBinding -> CorifyState -> CorifyState
bindFunctor name old functor state =
  let current = updateNormal state $ \scope -> scope {normalFunctors = Map.insert name functor (normalFunctors scope)}
   in current {stateFunctors = Map.insert old functor (stateFunctors current)}

insertStructure :: String -> Flat -> Flat -> Flat
insertStructure name inner (NormalFlat scope) =
  -- A nested functor may reuse the same formal name as an enclosing functor.
  -- The inner closure is the lexically nearer binding and must remain visible
  -- in the result signature (for example, F4(M) = F1(struct type t = int end)
  -- when both formals are named M).
  NormalFlat scope {normalStructures = Map.insertWith (\_ existing -> existing) name inner (normalStructures scope)}
insertStructure _ _ flat@(ForeignFlat _) = flat

aliasCon :: E.GlobalId -> GlobalId -> CorifyState -> CorifyState
aliasCon old target state = state {stateCons = Map.insert old target (stateCons state)}

aliasValue :: E.GlobalId -> ValueTarget -> CorifyState -> CorifyState
aliasValue old target state = state {stateValues = Map.insert old target (stateValues state)}

aliasConstructor :: E.GlobalId -> PatCon -> CorifyState -> CorifyState
aliasConstructor old target state = state {stateConstructors = Map.insert old target (stateConstructors state)}

aliasStructure :: E.GlobalId -> Flat -> CorifyState -> CorifyState
aliasStructure old target state = state {stateStructures = Map.insert old target (stateStructures state)}

aliasFunctor :: E.GlobalId -> FunctorBinding -> CorifyState -> CorifyState
aliasFunctor old target state = state {stateFunctors = Map.insert old target (stateFunctors state)}

enter :: [String] -> CorifyState -> CorifyState
enter path state = state {stateCurrent = emptyNormal path, stateParents = stateCurrent state : stateParents state}

leave :: CorifyState -> Maybe (Flat, CorifyState)
leave state = case stateParents state of
  [] -> Nothing
  parent : rest -> Just (stateCurrent state, state {stateCurrent = parent, stateParents = rest})

lookupConId :: E.GlobalId -> CorifyState -> Maybe GlobalId
lookupConId identifier = Map.lookup identifier . stateCons

lookupConDefinition :: E.GlobalId -> CorifyState -> Maybe E.Con
lookupConDefinition identifier = Map.lookup identifier . stateConDefinitions

lookupForeignCon :: E.GlobalId -> CorifyState -> Maybe (String, String)
lookupForeignCon identifier = Map.lookup identifier . stateForeignCons

lookupValueId :: E.GlobalId -> CorifyState -> Maybe ValueTarget
lookupValueId identifier = Map.lookup identifier . stateValues

lookupConstructorId :: E.GlobalId -> CorifyState -> Maybe PatCon
lookupConstructorId identifier = Map.lookup identifier . stateConstructors

lookupStructureId :: E.GlobalId -> CorifyState -> Maybe Flat
lookupStructureId identifier = Map.lookup identifier . stateStructures

lookupFunctorId :: E.GlobalId -> CorifyState -> Maybe FunctorBinding
lookupFunctorId identifier = Map.lookup identifier . stateFunctors

lookupConName :: String -> Flat -> Maybe ConTarget
lookupConName name flat = case flat of
  NormalFlat scope -> NormalCon <$> Map.lookup name (normalCons scope)
  ForeignFlat scope -> Just (ForeignCon (foreignScopeModule scope))

lookupValueName :: String -> Flat -> Maybe ValueTarget
lookupValueName name flat = case flat of
  NormalFlat scope -> Map.lookup name (normalValues scope)
  ForeignFlat scope -> ForeignValue (foreignScopeModule scope) name <$> Map.lookup name (foreignScopeValues scope)

lookupConstructorName :: String -> Flat -> Maybe PatCon
lookupConstructorName name flat = case flat of
  NormalFlat scope -> Map.lookup name (normalConstructors scope)
  ForeignFlat scope -> Map.lookup name (foreignScopeConstructors scope)

lookupStructureName :: String -> Flat -> Maybe Flat
lookupStructureName name (NormalFlat scope) = Map.lookup name (normalStructures scope)
lookupStructureName _ (ForeignFlat _) = Nothing

lookupFunctorName :: String -> Flat -> Maybe FunctorBinding
lookupFunctorName name (NormalFlat scope) = Map.lookup name (normalFunctors scope)
lookupFunctorName _ (ForeignFlat _) = Nothing

projectPath :: Flat -> [String] -> Maybe Flat
projectPath = foldl step . Just
  where
    step Nothing _ = Nothing
    step (Just flat) name = lookupStructureName name flat

scopePath :: CorifyState -> [String]
scopePath state = case stateCurrent state of
  NormalFlat scope -> normalPath scope
  ForeignFlat scope -> [foreignScopeModule scope]

describeFlat :: Flat -> String
describeFlat flat = case flat of
  NormalFlat scope ->
    "structure " <> show (normalPath scope)
      <> " with constructors " <> show (Map.keys (normalCons scope))
  ForeignFlat scope -> "foreign structure " <> foreignScopeModule scope

updateNormal :: CorifyState -> (NormalScope -> NormalScope) -> CorifyState
updateNormal state change = case stateCurrent state of
  NormalFlat scope -> state {stateCurrent = NormalFlat (change scope)}
  ForeignFlat _ -> error "attempted to bind inside a foreign structure"
