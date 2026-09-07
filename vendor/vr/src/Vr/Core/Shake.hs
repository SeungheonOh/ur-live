{-# LANGUAGE DerivingStrategies #-}

-- | Remove Core constructor and value declarations unreachable from observable
-- program roots.  This follows Ur/Web's Core @Shake@ boundary: exports,
-- database objects, tasks, policies, and the configured error handler are
-- roots; ordinary globals are retained only through transitive references.
module Vr.Core.Shake
  ( shakeFile
  ) where

import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Vr.Core.Syntax as C
import Vr.Source (Located (..))

data References = References
  { referenceValues :: !IntSet.IntSet
  , referenceConstructors :: !IntSet.IntSet
  }
  deriving stock (Eq, Show)

instance Semigroup References where
  References av ac <> References bv bc = References (av <> bv) (ac <> bc)

instance Monoid References where
  mempty = References IntSet.empty IntSet.empty

-- Global identities are integers. Keep the private reachability graph in
-- integer-keyed collections without changing AST identities or root order.
data ValueDefinition = ValueDefinition
  { definitionGroup :: !IntSet.IntSet
  , definitionReferences :: !References
  }

shakeFile :: C.File -> C.File
shakeFile file = filter retained file
  where
    constructorDefinitions = IntMap.fromList (concatMap constructorDefinition file)
    valueDefinitions = IntMap.fromList (concatMap valueDefinition file)
    roots = mconcat (map rootReferences file)
    live = close constructorDefinitions valueDefinitions roots
    retained declaration = case locatedValue declaration of
      C.DCon _ identifier _ _ -> IntSet.member (C.unGlobalId identifier) (referenceConstructors live)
      C.DDatatype definitions -> any (\(_, identifier, _, _) -> IntSet.member (C.unGlobalId identifier) (referenceConstructors live)) definitions
      C.DVal _ identifier _ _ _ -> IntSet.member (C.unGlobalId identifier) (referenceValues live)
      C.DValRec bindings -> any (\(_, identifier, _, _, _) -> IntSet.member (C.unGlobalId identifier) (referenceValues live)) bindings
      _ -> True

close
  :: IntMap.IntMap References
  -> IntMap.IntMap ValueDefinition
  -> References
  -> References
close constructorDefinitions valueDefinitions initial =
  go initial
    (referenceValues initial)
    (referenceConstructors initial)
    IntSet.empty
    IntSet.empty
  where
    -- A declaration dependency graph can be a long chain (the vendored utf8
    -- application is a representative case).  Recomputing dependencies for
    -- every member of the growing reachable set on each fixed-point round is
    -- quadratic.  This worklist computes the identical transitive closure
    -- while inspecting each reachable constructor and value at most once.
    go reachable pendingValues pendingConstructors seenValues seenConstructors =
      case IntSet.minView pendingValues of
        Just (identifier, remainingValues)
          | IntSet.member identifier seenValues ->
              go reachable remainingValues pendingConstructors seenValues seenConstructors
          | otherwise ->
              let discovered = case IntMap.lookup identifier valueDefinitions of
                    Just definition ->
                      definitionReferences definition
                        <> References (definitionGroup definition) IntSet.empty
                    Nothing -> mempty
                  reachable' = reachable <> discovered
               in go reachable'
                    (remainingValues <> referenceValues discovered)
                    (pendingConstructors <> referenceConstructors discovered)
                    (IntSet.insert identifier seenValues)
                    seenConstructors
        Nothing -> case IntSet.minView pendingConstructors of
          Just (identifier, remainingConstructors)
            | IntSet.member identifier seenConstructors ->
                go reachable pendingValues remainingConstructors seenValues seenConstructors
            | otherwise ->
                let discovered = IntMap.findWithDefault mempty identifier constructorDefinitions
                    reachable' = reachable <> discovered
                 in go reachable'
                      (pendingValues <> referenceValues discovered)
                      (remainingConstructors <> referenceConstructors discovered)
                      seenValues
                      (IntSet.insert identifier seenConstructors)
          Nothing -> reachable

constructorDefinition :: C.Decl -> [(Int, References)]
constructorDefinition declaration = case locatedValue declaration of
  C.DCon _ identifier _ definition -> [(C.unGlobalId identifier, conReferences definition)]
  C.DDatatype definitions ->
    [ (C.unGlobalId identifier, mconcat [maybe mempty conReferences payload | (_, _, payload) <- constructors])
    | (_, identifier, _, constructors) <- definitions
    ]
  _ -> []

valueDefinition :: C.Decl -> [(Int, ValueDefinition)]
valueDefinition declaration = case locatedValue declaration of
  C.DVal _ identifier typ expression _ ->
    [(C.unGlobalId identifier, ValueDefinition (IntSet.singleton (C.unGlobalId identifier)) (conReferences typ <> exprReferences expression))]
  C.DValRec bindings ->
    let group = IntSet.fromList [C.unGlobalId identifier | (_, identifier, _, _, _) <- bindings]
     in [ (C.unGlobalId identifier, ValueDefinition group (conReferences typ <> exprReferences expression))
        | (_, identifier, typ, expression, _) <- bindings
        ]
  C.DTable _ identifier row _ primary keys constraints uniques ->
    [(C.unGlobalId identifier, ValueDefinition (IntSet.singleton (C.unGlobalId identifier)) (conReferences row <> exprReferences primary <> conReferences keys <> exprReferences constraints <> conReferences uniques))]
  C.DSequence _ identifier _ ->
    [(C.unGlobalId identifier, ValueDefinition (IntSet.singleton (C.unGlobalId identifier)) mempty)]
  C.DView _ identifier _ expression row ->
    [(C.unGlobalId identifier, ValueDefinition (IntSet.singleton (C.unGlobalId identifier)) (exprReferences expression <> conReferences row))]
  C.DCookie _ identifier typ _ ->
    [(C.unGlobalId identifier, ValueDefinition (IntSet.singleton (C.unGlobalId identifier)) (conReferences typ))]
  C.DStyle _ identifier _ ->
    [(C.unGlobalId identifier, ValueDefinition (IntSet.singleton (C.unGlobalId identifier)) mempty)]
  _ -> []

rootReferences :: C.Decl -> References
rootReferences declaration = case locatedValue declaration of
  C.DForeign _ _ typ -> conReferences typ
  C.DExport _ identifier _ -> valueReference identifier
  C.DTable _ _ row _ primary keys constraints uniques ->
    conReferences row <> exprReferences primary <> conReferences keys <> exprReferences constraints <> conReferences uniques
  C.DView _ _ _ expression row -> exprReferences expression <> conReferences row
  C.DIndex table modes -> exprReferences table <> exprReferences modes
  C.DTask kind body -> exprReferences kind <> exprReferences body
  C.DPolicy expression -> exprReferences expression
  C.DOnError identifier -> valueReference identifier
  _ -> mempty

valueReference :: C.GlobalId -> References
valueReference identifier = References (IntSet.singleton (C.unGlobalId identifier)) IntSet.empty

conReferences :: C.Con -> References
conReferences = References IntSet.empty . go IntSet.empty
  where
    -- Constructors cannot reference values. Accumulate their named type IDs
    -- directly instead of allocating a pair of sets at every interior node.
    go !known constructor = case locatedValue constructor of
      C.CNamed identifier -> IntSet.insert (C.unGlobalId identifier) known
      C.TFun domain range -> go (go known domain) range
      C.TCFun _ _ body -> go known body
      C.TRecord row -> go known row
      C.CApp function argument -> go (go known function) argument
      C.CAbs _ _ body -> go known body
      C.CKAbs _ body -> go known body
      C.CKApp function _ -> go known function
      C.TKFun _ body -> go known body
      C.CRecord _ fields -> foldl' (\found (name, value) -> go (go found name) value) known fields
      C.CConcat left right -> go (go known left) right
      C.CTuple elements -> foldl' go known elements
      C.CProj tuple _ -> go known tuple
      _ -> known

exprReferences :: C.Expr -> References
exprReferences expression = case locatedValue expression of
  C.ENamed identifier -> valueReference identifier
  C.ECon _ constructor arguments payload -> patConReferences constructor <> mconcat (map conReferences arguments) <> maybe mempty exprReferences payload
  C.EFfiApp _ _ arguments -> mconcat [exprReferences value <> conReferences typ | (value, typ) <- arguments]
  C.EApp function argument -> exprReferences function <> exprReferences argument
  C.EAbs _ domain range body -> conReferences domain <> conReferences range <> exprReferences body
  C.ECApp function argument -> exprReferences function <> conReferences argument
  C.ECAbs _ _ body -> exprReferences body
  C.EKAbs _ body -> exprReferences body
  C.EKApp function _ -> exprReferences function
  C.ERecord fields -> mconcat [conReferences name <> exprReferences value <> conReferences typ | (name, value, typ) <- fields]
  C.EField record field typ rest -> exprReferences record <> conReferences field <> conReferences typ <> conReferences rest
  C.EConcat left leftRow right rightRow -> exprReferences left <> conReferences leftRow <> exprReferences right <> conReferences rightRow
  C.ECut record field typ rest -> exprReferences record <> conReferences field <> conReferences typ <> conReferences rest
  C.ECutMulti record fields rest -> exprReferences record <> conReferences fields <> conReferences rest
  C.ECase scrutinee branches input result ->
    exprReferences scrutinee <> mconcat [patternReferences pattern' <> exprReferences body | (pattern', body) <- branches] <> conReferences input <> conReferences result
  C.EWrite value -> exprReferences value
  C.EClosure identifier captures -> valueReference identifier <> mconcat (map exprReferences captures)
  C.ELet _ typ value body -> conReferences typ <> exprReferences value <> exprReferences body
  C.EServerCall identifier arguments typ _ -> valueReference identifier <> mconcat (map exprReferences arguments) <> conReferences typ
  _ -> mempty

patternReferences :: C.Pattern -> References
patternReferences pattern' = case locatedValue pattern' of
  C.PVar _ typ -> conReferences typ
  C.PCon _ constructor arguments nested -> patConReferences constructor <> mconcat (map conReferences arguments) <> maybe mempty patternReferences nested
  C.PRecord fields -> mconcat [patternReferences nested <> conReferences typ | (_, nested, typ) <- fields]
  C.PPrim {} -> mempty

patConReferences :: C.PatCon -> References
patConReferences constructor = case constructor of
  C.PConFfi _ _ _ _ payload _ -> maybe mempty conReferences payload
  C.PConVar {} -> mempty
