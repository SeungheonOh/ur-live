{-# LANGUAGE DerivingStrategies #-}

-- | Module-free, explicitly typed whole-program Core language.  Structures,
-- signatures, and module projections have been flattened; polymorphism is
-- retained for specialization.
module Vr.Core.Syntax
  ( GlobalId (..)
  , DatatypeKind (..)
  , Kind
  , KindF (..)
  , Con
  , ConF (..)
  , PatCon (..)
  , Pattern
  , PatternF (..)
  , Expr
  , ExprF (..)
  , Decl
  , DeclF (..)
  , File
  ) where

import Vr.Elaborate.Syntax (DatatypeKind (..), GlobalId (..))
import Vr.Middle (ExportKind, FailureMode)
import Vr.Source (Located, Primitive)

type Kind = Located KindF

data KindF
  = KType
  | KArrow !Kind !Kind
  | KName
  | KRecord !Kind
  | KUnit
  | KTuple ![Kind]
  | KRel !Int
  | KFun !String !Kind
  deriving stock (Eq, Ord, Show)

type Con = Located ConF

data ConF
  = TFun !Con !Con
  | TCFun !String !Kind !Con
  | TRecord !Con
  | CRel !Int
  | CNamed !GlobalId
  | CFfi !String !String
  | CApp !Con !Con
  | CAbs !String !Kind !Con
  | CKAbs !String !Con
  | CKApp !Con !Kind
  | TKFun !String !Con
  | CName !String
  | CRecord !Kind ![(Con, Con)]
  | CConcat !Con !Con
  | CMap !Kind !Kind
  | CUnit
  | CTuple ![Con]
  | CProj !Con !Int
  deriving stock (Eq, Ord, Show)

data PatCon
  = PConVar !GlobalId
  | PConFfi !String !String ![String] !String !(Maybe Con) !DatatypeKind
  deriving stock (Eq, Ord, Show)

type Pattern = Located PatternF

data PatternF
  = PVar !String !Con
  | PPrim !Primitive
  | PCon !DatatypeKind !PatCon ![Con] !(Maybe Pattern)
  | PRecord ![(String, Pattern, Con)]
  deriving stock (Eq, Ord, Show)

type Expr = Located ExprF

data ExprF
  = EPrim !Primitive
  | ERel !Int
  | ENamed !GlobalId
  | ECon !DatatypeKind !PatCon ![Con] !(Maybe Expr)
  | EFfi !String !String
  | EFfiApp !String !String ![(Expr, Con)]
  | EApp !Expr !Expr
  | EAbs !String !Con !Con !Expr
  | ECApp !Expr !Con
  | ECAbs !String !Kind !Expr
  | EKAbs !String !Expr
  | EKApp !Expr !Kind
  | ERecord ![(Con, Expr, Con)]
  | EField !Expr !Con !Con !Con
  | EConcat !Expr !Con !Expr !Con
  | ECut !Expr !Con !Con !Con
  | ECutMulti !Expr !Con !Con
  | ECase !Expr ![(Pattern, Expr)] !Con !Con
  | EWrite !Expr
  | EClosure !GlobalId ![Expr]
  | ELet !String !Con !Expr !Expr
  | EServerCall !GlobalId ![Expr] !Con !FailureMode
  deriving stock (Eq, Ord, Show)

type Decl = Located DeclF

data DeclF
  = DCon !String !GlobalId !Kind !Con
  -- | A foreign value's ABI signature.  Expressions still refer to it with
  -- 'EFfi'; this declaration preserves the type for target backends.
  | DForeign !String !String !Con
  | DDatatype ![(String, GlobalId, [String], [(String, GlobalId, Maybe Con)])]
  | DVal !String !GlobalId !Con !Expr !String
  | DValRec ![(String, GlobalId, Con, Expr, String)]
  | DExport !ExportKind !GlobalId !Bool
  | DTable !String !GlobalId !Con !String !Expr !Con !Expr !Con
  | DSequence !String !GlobalId !String
  | DView !String !GlobalId !String !Expr !Con
  | DIndex !Expr !Expr
  | DDatabase !String
  | DCookie !String !GlobalId !Con !String
  | DStyle !String !GlobalId !String
  | DTask !Expr !Expr
  | DPolicy !Expr
  | DOnError !GlobalId
  deriving stock (Eq, Ord, Show)

type File = [Decl]
