{-# LANGUAGE DerivingStrategies #-}

-- | The post-Unnest, post-Explify language.  Unlike the elaboration tree,
-- this datatype cannot represent inference variables, recovery nodes,
-- disjointness evidence, class-only signature items, or local recursive
-- declarations.
module Vr.Explicit.Syntax
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
  , Signature
  , SignatureF (..)
  , SigItem
  , SigItemF (..)
  , Decl
  , DeclF (..)
  , Structure
  , StructureF (..)
  , File
  ) where

import Vr.Elaborate.Syntax (DatatypeKind (..), GlobalId (..))
import Vr.Source (Located, Primitive, SFfiMode)

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
  | CModProj !GlobalId ![String] !String
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
  | PConProj !GlobalId ![String] !String
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
  | EModProj !GlobalId ![String] !String
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
  | ELet !String !Con !Expr !Expr
  deriving stock (Eq, Ord, Show)

type SigItem = Located SigItemF

data SigItemF
  = SgiConAbs !String !GlobalId !Kind
  | SgiCon !String !GlobalId !Kind !Con
  | SgiDatatype ![(String, GlobalId, [String], [(String, GlobalId, Maybe Con)])]
  | SgiDatatypeImp !String !GlobalId !GlobalId ![String] !String ![String] ![(String, GlobalId, Maybe Con)]
  | SgiVal !String !GlobalId !Con
  | SgiStr !String !GlobalId !Signature
  | SgiSgn !String !GlobalId !Signature
  deriving stock (Eq, Ord, Show)

type Signature = Located SignatureF

data SignatureF
  = SgnConst ![SigItem]
  | SgnVar !GlobalId
  | SgnFun !String !GlobalId !Signature !Signature
  | SgnWhere !Signature ![String] !String !Con
  | SgnProj !GlobalId ![String] !String
  deriving stock (Eq, Ord, Show)

type Decl = Located DeclF

data DeclF
  = DCon !String !GlobalId !Kind !Con
  | DDatatype ![(String, GlobalId, [String], [(String, GlobalId, Maybe Con)])]
  | DDatatypeImp !String !GlobalId !GlobalId ![String] !String ![String] ![(String, GlobalId, Maybe Con)]
  | DVal !String !GlobalId !Con !Expr
  | DValRec ![(String, GlobalId, Con, Expr)]
  | DSgn !String !GlobalId !Signature
  | DStr !String !GlobalId !Signature !Structure
  | DFfiStr !String !GlobalId !Signature
  | DExport !GlobalId !Signature !Structure
  | DTable !GlobalId !String !GlobalId !Con !Expr !Con !Expr !Con
  | DSequence !GlobalId !String !GlobalId
  | DView !GlobalId !String !GlobalId !Expr !Con
  | DIndex !Expr !Expr
  | DDatabase !String
  | DCookie !GlobalId !String !GlobalId !Con
  | DStyle !GlobalId !String !GlobalId
  | DTask !Expr !Expr
  | DPolicy !Expr
  | DOnError !GlobalId ![String] !String
  | DFfi !String !GlobalId ![SFfiMode] !Con
  deriving stock (Eq, Ord, Show)

type Structure = Located StructureF

data StructureF
  = StrConst ![Decl]
  | StrVar !GlobalId
  | StrProj !Structure !String
  | StrFun !String !GlobalId !Signature !Signature !Structure
  | StrApp !Structure !Structure
  deriving stock (Eq, Ord, Show)

type File = [Decl]
