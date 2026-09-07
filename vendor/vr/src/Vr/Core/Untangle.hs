-- | Split recursive value groups into strongly connected components.
--
-- Ur's surface @fun@ syntax enters Core as a recursive group even when its
-- body never calls itself.  The reference compiler performs this pass before
-- reduction, which is important: an acyclic polymorphic function becomes an
-- ordinary 'C.DVal' and is then eligible for the reducer's polymorphic-inline
-- rule.
module Vr.Core.Untangle
  ( untangleFile
  ) where

import Data.Graph (SCC (..), stronglyConnComp)
import qualified Data.Set as Set
import qualified Vr.Core.Syntax as C
import Vr.Source (Located (..))

type Binding = (String, C.GlobalId, C.Con, C.Expr, String)

untangleFile :: C.File -> C.File
untangleFile = concatMap untangleDeclaration

untangleDeclaration :: C.Decl -> [C.Decl]
untangleDeclaration declaration = case locatedValue declaration of
  C.DValRec bindings -> map component (stronglyConnComp nodes)
    where
      group = Set.fromList [identifier | (_, identifier, _, _, _) <- bindings]
      nodes =
        [ (binding, identifier, Set.toList (Set.intersection group (valueReferences expression)))
        | binding@(_, identifier, _, expression, _) <- bindings
        ]
      component scc = declaration {locatedValue = case scc of
        AcyclicSCC binding -> bindingValue binding
        CyclicSCC recursive -> C.DValRec recursive}
  _ -> [declaration]

bindingValue :: Binding -> C.DeclF
bindingValue (name, identifier, typ, expression, url) =
  C.DVal name identifier typ expression url

valueReferences :: C.Expr -> Set.Set C.GlobalId
valueReferences expression = direct <> children
  where
    direct = case locatedValue expression of
      C.ENamed identifier -> Set.singleton identifier
      C.EClosure identifier _ -> Set.singleton identifier
      C.EServerCall identifier _ _ _ -> Set.singleton identifier
      _ -> Set.empty
    children = case locatedValue expression of
      C.ECon _ _ _ payload -> maybe Set.empty valueReferences payload
      C.EFfiApp _ _ arguments -> unions [valueReferences value | (value, _) <- arguments]
      C.EApp function argument -> valueReferences function <> valueReferences argument
      C.EAbs _ _ _ body -> valueReferences body
      C.ECApp function _ -> valueReferences function
      C.ECAbs _ _ body -> valueReferences body
      C.EKAbs _ body -> valueReferences body
      C.EKApp function _ -> valueReferences function
      C.ERecord fields -> unions [valueReferences value | (_, value, _) <- fields]
      C.EField record _ _ _ -> valueReferences record
      C.EConcat left _ right _ -> valueReferences left <> valueReferences right
      C.ECut record _ _ _ -> valueReferences record
      C.ECutMulti record _ _ -> valueReferences record
      C.ECase scrutinee branches _ _ -> valueReferences scrutinee <> unions (map (valueReferences . snd) branches)
      C.EWrite value -> valueReferences value
      C.EClosure _ captures -> unions (map valueReferences captures)
      C.ELet _ _ value body -> valueReferences value <> valueReferences body
      C.EServerCall _ arguments _ _ -> unions (map valueReferences arguments)
      _ -> Set.empty
    unions = Set.unions
