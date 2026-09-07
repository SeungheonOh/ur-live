{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE MagicHash #-}

-- | Target-independent monomorphic Ur IR.  There are no kinds,
-- constructors, modules, or type abstractions.  Web, SQL, transaction,
-- reactive, and RPC behavior remains explicit for later direct-JavaScript,
-- LLVM, or other target lowerings.
module Vr.Mono.Syntax
  ( GlobalId (..)
  , DatatypeKind (..)
  , Type
  , TypeF (..)
  , PatCon (..)
  , Pattern
  , PatternF (..)
  , JavaScriptMode (..)
  , BinopIntness (..)
  , StaticArg (..)
  , SqlCacheFlush (..)
  , Expr
  , ExprF (..)
  , Policy (..)
  , IndexMode (..)
  , DatabaseInfo (..)
  , Decl
  , DeclF (..)
  , File (..)
  ) where

import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)
import Vr.Elaborate.Syntax (DatatypeKind (..), GlobalId (..))
import Vr.Middle (DbMode, Effect, ExportKind, FailureMode, Sidedness)
import Vr.Source (Located, Primitive)

type Type = Located TypeF

data TypeF
  = TFun !Type !Type
  | TRecord ![(String, Type)]
  | TDatatype !GlobalId
  | TFfi !String !String
  | TOption !Type
  | TList !Type
  | TSource
  | TSignal !Type
  deriving stock (Show)

-- Like StaticArg below, Mono types are finite, reflexive structural data.
-- Keep the old constructor/field ordering while skipping shared subtrees.
instance Eq TypeF where
  left == right = compare left right == EQ

instance Ord TypeF where
  compare left right = left `seq` right `seq`
    if isTrue# (reallyUnsafePtrEquality# left right) then EQ else structural left right
    where
      structural (TFun ad ar) (TFun bd br) = compare ad bd <> compare ar br
      structural (TRecord a) (TRecord b) = compare a b
      structural (TDatatype a) (TDatatype b) = compare a b
      structural (TFfi am an) (TFfi bm bn) = compare am bm <> compare an bn
      structural (TOption a) (TOption b) = compare a b
      structural (TList a) (TList b) = compare a b
      structural TSource TSource = EQ
      structural (TSignal a) (TSignal b) = compare a b
      structural a b = compare (constructorOrder a) (constructorOrder b)
      constructorOrder :: TypeF -> Int
      constructorOrder typ = case typ of
        TFun {} -> 0
        TRecord {} -> 1
        TDatatype {} -> 2
        TFfi {} -> 3
        TOption {} -> 4
        TList {} -> 5
        TSource -> 6
        TSignal {} -> 7

data PatCon
  = PConVar !GlobalId
  | PConFfi !String !String !String !(Maybe Type)
  deriving stock (Eq, Ord, Show)

type Pattern = Located PatternF

data PatternF
  = PVar !String !Type
  | PPrim !Primitive
  | PCon !DatatypeKind !PatCon !(Maybe Pattern)
  | PRecord ![(String, Pattern, Type)]
  | PNone !Type
  | PSome !Type !Pattern
  deriving stock (Eq, Ord, Show)

data JavaScriptMode
  = JavaScriptAttribute
  | JavaScriptScript
  | JavaScriptSource !Type
  deriving stock (Eq, Ord, Show)

data BinopIntness = IntegerBinop | GeneralBinop
  deriving stock (Eq, Ord, Show)

-- | A fully resolved compile-time argument to a runtime intrinsic.  Keeping
-- these operands is important for direct backends: record labels and concrete
-- types may affect an intrinsic even though no runtime type abstraction
-- remains in Mono.
data StaticArg
  = StaticType !Type
  | StaticName !String
  | StaticRow ![(StaticArg, StaticArg)]
  | StaticTuple ![StaticArg]
  | StaticFfi !String !String ![StaticArg]
  | StaticMap
  | StaticBound !Int
  | StaticLambda !StaticArg
  | StaticApply !StaticArg !StaticArg
  | StaticProject !StaticArg !Int
  | StaticConcat !StaticArg !StaticArg
  | StaticUnit
  deriving stock (Show)

-- Static arguments contain only finite, reflexively comparable type/name
-- data, never floating-point literals. Lowered expressions often share large
-- row arguments. A positive identity check can skip their repeated traversal;
-- a negative result still performs the exact original structural comparison.
instance Eq StaticArg where
  left == right = compare left right == EQ

instance Ord StaticArg where
  compare left right = left `seq` right `seq`
    if isTrue# (reallyUnsafePtrEquality# left right) then EQ else structural left right
    where
      structural (StaticType a) (StaticType b) = compare a b
      structural (StaticName a) (StaticName b) = compare a b
      structural (StaticRow a) (StaticRow b) = compare a b
      structural (StaticTuple a) (StaticTuple b) = compare a b
      structural (StaticFfi am an aa) (StaticFfi bm bn ba) =
        compare am bm <> compare an bn <> compare aa ba
      structural StaticMap StaticMap = EQ
      structural (StaticBound a) (StaticBound b) = compare a b
      structural (StaticLambda a) (StaticLambda b) = compare a b
      structural (StaticApply af aa) (StaticApply bf ba) = compare af bf <> compare aa ba
      structural (StaticProject a ai) (StaticProject b bi) = compare a b <> compare ai bi
      structural (StaticConcat al ar) (StaticConcat bl br) = compare al bl <> compare ar br
      structural StaticUnit StaticUnit = EQ
      structural a b = compare (constructorOrder a) (constructorOrder b)
      -- Preserve the declaration order used by the derived Ord instance.
      constructorOrder :: StaticArg -> Int
      constructorOrder argument = case argument of
        StaticType {} -> 0
        StaticName {} -> 1
        StaticRow {} -> 2
        StaticTuple {} -> 3
        StaticFfi {} -> 4
        StaticMap -> 5
        StaticBound {} -> 6
        StaticLambda {} -> 7
        StaticApply {} -> 8
        StaticProject {} -> 9
        StaticConcat {} -> 10
        StaticUnit -> 11

-- | One invalidation emitted before a database modification.  The numeric
-- cache identity names a compiler-generated query cache.  Each key position
-- is either a known URL-serialized value or 'Nothing', which denotes every
-- value below that prefix.  Keeping the invalidation shape in Mono lets every
-- server backend share the same dependency decision while choosing its own
-- concurrent cache representation.
data SqlCacheFlush = SqlCacheFlush
  { sqlCacheFlushIndex :: !Int
  , sqlCacheFlushKeys :: ![Maybe Expr]
  }
  deriving stock (Eq, Ord, Show)

type Expr = Located ExprF

data ExprF
  = EPrim !Primitive
  | ERel !Int
  | ENamed !GlobalId
  | ECon !DatatypeKind !PatCon !(Maybe Expr)
  | ENone !Type
  | ESome !Type !Expr
  | EFfi !String !String ![StaticArg]
  | EFfiApp !String !String ![StaticArg] ![(Expr, Type)]
  | EApp !Expr !Expr
  | EAbs !String !Type !Type !Expr
  | EStaticApp !Expr !StaticArg
  | EUnop !String !Expr
  | EBinop !BinopIntness !String !Expr !Expr
  | ERecord ![(StaticArg, Expr, Type)]
  | EField !Expr !StaticArg
  | ERecordConcat !Expr !Expr
  | ERecordCut !Expr ![StaticArg]
  | ECase !Expr ![(Pattern, Expr)] !Type !Type
  | EStrcat !Expr !Expr
  | EError !Expr !Type
  | EReturnBlob !(Maybe Expr) !Expr !Type
  | ERedirect !Expr !Type
  | EWrite !Expr
  | ESeq !Expr !Expr
  | ELet !String !Type !Expr !Expr
  | EClosure !GlobalId ![Expr]
  | EQuery ![(String, Type)] ![(String, [(String, Type)])] !Type !Expr !Expr !Expr
  | EDml !Expr !FailureMode
  | ENextval !Expr
  | ESetval !Expr !Expr
  | EUnurlify !Expr !Type !Bool
  | EJavaScript !JavaScriptMode !Expr
  | ESignalReturn !Expr
  | ESignalBind !Expr !Expr
  | ESignalSource !Expr
  | EServerCall !Expr !Type !Effect !FailureMode
  | ERecv !Expr !Type
  | ESleep !Expr
  | ESpawn !Expr
  -- | Transactional memoization of a pure server expression influenced by an
  -- SQL query.  The fields are the compiler-assigned cache identity, the
  -- monomorphic result type used for serialization, ordered cache-key
  -- expressions, and the original transaction action.  A miss records page
  -- and script output and stages the serialized result for installation only
  -- after the enclosing database transaction commits; a hit replays those
  -- outputs and decodes the saved result.
  | ESqlCache !Int !Type ![Expr] !Expr
  -- | Run ordered SQL-cache invalidations before the enclosed transaction
  -- action.  The first field is the transaction's result type, needed by
  -- backends when they materialize the invalidation wrapper as a unit thunk.
  -- Invalidations take effect immediately (an aborted transaction may
  -- therefore cause harmless extra misses), matching Ur/Web's rule that a
  -- later store in the same transaction must not resurrect stale data.
  | ESqlCacheFlush !Type ![SqlCacheFlush] !Expr
  deriving stock (Eq, Ord, Show)

data Policy
  = PolicyClient !Expr
  | PolicyInsert !Expr
  | PolicyDelete !Expr
  | PolicyUpdate !Expr
  | PolicySequence !Expr
  deriving stock (Eq, Ord, Show)

data IndexMode = IndexEquality | IndexTrigram | IndexSkipped
  deriving stock (Eq, Ord, Show)

data DatabaseInfo = DatabaseInfo
  { databaseName :: !String
  , databaseExpunge :: !GlobalId
  , databaseInitialize :: !GlobalId
  , databaseUsesSimilar :: !Bool
  }
  deriving stock (Eq, Ord, Show)

type Decl = Located DeclF

data DeclF
  = DForeign !String !String !Type
    -- ^ Monomorphic foreign-value ABI metadata: module, member, and complete
    -- curried Ur type.  It allocates no runtime global by itself.
  | DDatatype ![(String, GlobalId, [(String, GlobalId, Maybe Type)])]
  | DVal !String !GlobalId !Type !Expr !String
  | DValRec ![(String, GlobalId, Type, Expr, String)]
  | DExport !ExportKind !String !GlobalId ![Type] !Type !Bool
  | DTable !String ![(String, Type)] !Expr !Expr
  | DSequence !String
  | DView !String ![(String, Type)] !Expr
  | DIndex !String ![(String, IndexMode)]
  | DIndexDynamic !Expr !Expr
  | DDatabase !DatabaseInfo
  | DDatabaseRaw !String
  | DJavaScript !String
  | DCookie !String
  | DStyle !String
  | DTask !Expr !Expr
  | DPolicy !Policy
  | DPolicyRaw !Expr
  | DOnError !GlobalId
  deriving stock (Eq, Ord, Show)

data File = File
  { fileDeclarations :: ![Decl]
  , fileFunctionModes :: ![(GlobalId, Sidedness, DbMode)]
  }
  deriving stock (Eq, Ord, Show)
