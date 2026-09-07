-- | Disjointness facts and proofs.  Constructor names are decomposed from rows
-- (including projections and mapped rows), while opaque pieces remain delayed
-- until constructor inference has made progress.
module Vr.Elaborate.Disjoint
  ( assertDisjoint
  , requireDisjoint
  , solveDisjointConstraint
  , decomposeRow
  ) where

import Data.Char (toLower)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Vr.Elaborate.State
import Vr.Elaborate.Types
import Vr.Source (Located (..), Span)

data Piece = Piece !DisjointAtom | Unknown !Con

assertDisjoint :: Environment -> Con -> Con -> ElabM Environment
assertDisjoint environment left right = do
  leftPieces <- knownPieces <$> decomposeRow environment left
  rightPieces <- knownPieces <$> decomposeRow environment right
  let facts1 = foldl (insertAgainst rightPieces) (environmentDisjointFacts environment) leftPieces
      facts2 = foldl (insertAgainst leftPieces) facts1 rightPieces
  pure environment {environmentDisjointFacts = facts2}
  where
    insertAgainst others facts atom =
      let relevant = case atom of
            DisjointName {} -> filter (not . isLiteralName) others
            _ -> others
       in Map.insertWith Set.union atom (Set.fromList relevant) facts

requireDisjoint :: Environment -> Con -> Con -> Span -> ElabM ()
requireDisjoint environment left right at = do
  outcome <- prove environment left right
  case outcome of
    Proved -> pure ()
    Deferred -> addConstraint (DisjointConstraint environment left right at)
    Refuted first second -> withSpanError "not-disjoint" at ("Record fragments overlap or lack a disjointness fact: " <> show first <> " and " <> show second)

solveDisjointConstraint :: Bool -> Constraint -> ElabM Bool
solveDisjointConstraint final constraint = case constraint of
  DisjointConstraint environment left right at -> do
    outcome <- prove environment left right
    case outcome of
      Proved -> pure True
      Deferred | not final -> pure False
      Deferred -> withSpanError "unresolved-disjoint" at ("Could not resolve disjointness of " <> show left <> " and " <> show right) >> pure True
      Refuted first second -> withSpanError "not-disjoint" at ("Could not prove " <> show first <> " disjoint from " <> show second) >> pure True
  _ -> pure False

data Proof = Proved | Deferred | Refuted !DisjointAtom !DisjointAtom

prove :: Environment -> Con -> Con -> ElabM Proof
prove environment left right = do
  leftPieces <- decomposeRow environment left
  rightPieces <- decomposeRow environment right
  if (hasUnknown leftPieces && not (null rightPieces)) || (hasUnknown rightPieces && not (null leftPieces))
    then pure Deferred
    else pure (provePairs (knownPieces leftPieces) (knownPieces rightPieces))
  where
    provePairs firsts seconds =
      case
        [ (first, second)
        | first <- firsts
        , second <- seconds
        , not (proveOne environment first second)
        , not (isMetaAtom first || isMetaAtom second)
        ] of
          (first, second) : _ -> Refuted first second
          []
            | or
                [ not (proveOne environment first second)
                | first <- firsts
                , second <- seconds
                ] -> Deferred
            | otherwise -> Proved

    isMetaAtom DisjointMeta {} = True
    isMetaAtom _ = False

proveOne :: Environment -> DisjointAtom -> DisjointAtom -> Bool
proveOne environment first second = case (first, second) of
  (DisjointName left projections, DisjointName right otherProjections) ->
    projections /= otherProjections || map toLower left /= map toLower right
  _ -> maybe False (Set.member second) (Map.lookup first (environmentDisjointFacts environment))

decomposeRow :: Environment -> Con -> ElabM [Piece]
decomposeRow environment constructor0 = do
  constructor <- headNormalizeCon environment constructor0
  case locatedValue constructor of
    CApp outer row -> case locatedValue outer of
      CApp mapper _ -> case locatedValue mapper of
        CMap {} -> decomposeRow environment row
        _ -> defaultPiece constructor
      _ -> defaultPiece constructor
    _ -> defaultPiece constructor
  where
    defaultPiece constructor = do
      (base, projections) <- peelProjections environment constructor
      case locatedValue base of
        CRecord _ fields -> concat <$> mapM (decomposeName environment . fst) fields
        CConcat left right -> (<>) <$> decomposeRow environment left <*> decomposeRow environment right
        CMeta identifier _ _ _ -> pure [Piece (DisjointMeta identifier projections)]
        CRel index -> pure [Piece (DisjointRelativeRow index projections)]
        CNamed identifier -> pure [Piece (DisjointNamedRow identifier projections)]
        CModProj identifier path name -> pure [Piece (DisjointProjectedRow identifier path name projections)]
        _ -> pure [Unknown constructor]

decomposeName :: Environment -> Con -> ElabM [Piece]
decomposeName environment constructor = do
  (base, projections) <- peelProjections environment constructor
  pure [case locatedValue base of
    CName name -> Piece (DisjointName name projections)
    CMeta identifier _ _ _ -> Piece (DisjointMeta identifier projections)
    CRel index -> Piece (DisjointRelativeName index projections)
    CNamed identifier -> Piece (DisjointNamedName identifier projections)
    CModProj identifier path name -> Piece (DisjointProjectedName identifier path name projections)
    _ -> Unknown constructor]

peelProjections :: Environment -> Con -> ElabM (Con, [Int])
peelProjections environment = go []
  where
    go projections constructor0 = do
      constructor <- headNormalizeCon environment constructor0
      case locatedValue constructor of
        CProj tuple index -> go (index : projections) tuple
        _ -> pure (constructor, projections)

knownPieces :: [Piece] -> [DisjointAtom]
knownPieces pieces = [piece | Piece piece <- pieces]

hasUnknown :: [Piece] -> Bool
hasUnknown = any isUnknown
  where
    isUnknown (Unknown _) = True
    isUnknown _ = False

isLiteralName :: DisjointAtom -> Bool
isLiteralName DisjointName {} = True
isLiteralName _ = False
