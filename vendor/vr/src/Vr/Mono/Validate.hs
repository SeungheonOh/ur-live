-- | Whole-file invariants for the backend handoff.  The Mono datatype already
-- makes kinds, constructors, and modules unrepresentable; this audit checks
-- the cross-declaration identities that a datatype alone cannot enforce.
module Vr.Mono.Validate
  ( validateFile
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Vr.Mono.Syntax as M
import Vr.Source (Diagnostic, DiagnosticPhase (MonoPhase), Located (..), Span, diagnostic)

data Globals = Globals
  { globalValues :: !(Set.Set M.GlobalId)
  , globalDatatypes :: !(Set.Set M.GlobalId)
  , globalConstructors :: !(Set.Set M.GlobalId)
  }

validateFile :: M.File -> Either [Diagnostic] M.File
validateFile file =
  let declarations = M.fileDeclarations file
      (globals, duplicates) = collectGlobals declarations
      problems = duplicates <> concatMap (validateDeclaration globals) declarations
   in if null problems then Right file else Left problems

collectGlobals :: [M.Decl] -> (Globals, [Diagnostic])
collectGlobals = finish . foldl collect (Map.empty, Map.empty, Map.empty, [])
  where
    collect (values, datatypes, constructors, problems) declaration = case locatedValue declaration of
      M.DDatatype definitions ->
        let (datatypes', constructors', problems') = foldl (datatype (locatedSpan declaration)) (datatypes, constructors, problems) definitions
         in (values, datatypes', constructors', problems')
      M.DVal _ identifier _ _ _ ->
        let (values', problems') = insertUnique "duplicate-value" "value" (locatedSpan declaration) identifier values problems
         in (values', datatypes, constructors, problems')
      M.DValRec bindings ->
        let (values', problems') = foldl (binding (locatedSpan declaration)) (values, problems) bindings
         in (values', datatypes, constructors, problems')
      _ -> (values, datatypes, constructors, problems)

    datatype location (datatypes, constructors, problems) (_, identifier, alternatives) =
      let (datatypes', problems') = insertUnique "duplicate-datatype" "datatype" location identifier datatypes problems
          (constructors', problems'') = foldl (constructor location) (constructors, problems') alternatives
       in (datatypes', constructors', problems'')

    constructor location (constructors, problems) (_, identifier, _) =
      insertUnique "duplicate-constructor" "datatype constructor" location identifier constructors problems

    binding location (values, problems) (_, identifier, _, _, _) =
      insertUnique "duplicate-value" "value" location identifier values problems

    finish (values, datatypes, constructors, problems) =
      (Globals (Map.keysSet values) (Map.keysSet datatypes) (Map.keysSet constructors), reverse problems)

insertUnique
  :: String
  -> String
  -> Span
  -> M.GlobalId
  -> Map.Map M.GlobalId Span
  -> [Diagnostic]
  -> (Map.Map M.GlobalId Span, [Diagnostic])
insertUnique code description location identifier known problems = case Map.lookup identifier known of
  Nothing -> (Map.insert identifier location known, problems)
  Just _ ->
    ( known
    , diagnostic MonoPhase code location
        ("Duplicate monomorphic " <> description <> " identity #" <> show (M.unGlobalId identifier))
        : problems
    )

validateDeclaration :: Globals -> M.Decl -> [Diagnostic]
validateDeclaration globals declaration = case locatedValue declaration of
  M.DForeign _ _ typ -> validateType globals typ
  M.DDatatype definitions -> concat
    [ maybe [] (validateType globals) payload
    | (_, _, alternatives) <- definitions
    , (_, _, payload) <- alternatives
    ]
  M.DVal _ _ typ expression _ -> validateType globals typ <> validateExpr globals expression
  M.DValRec bindings -> concat
    [ validateType globals typ <> validateExpr globals expression
    | (_, _, typ, expression, _) <- bindings
    ]
  M.DExport _ _ identifier arguments result _ ->
    requireValue globals (locatedSpan declaration) identifier
      <> concatMap (validateType globals) arguments
      <> validateType globals result
  M.DTable _ fields primary constraints ->
    concatMap (validateType globals . snd) fields
      <> validateExpr globals primary
      <> validateExpr globals constraints
  M.DView _ fields expression ->
    concatMap (validateType globals . snd) fields <> validateExpr globals expression
  M.DIndexDynamic table modes -> validateExpr globals table <> validateExpr globals modes
  M.DDatabase information ->
    requireValue globals (locatedSpan declaration) (M.databaseExpunge information)
      <> requireValue globals (locatedSpan declaration) (M.databaseInitialize information)
  M.DTask kind body -> validateExpr globals kind <> validateExpr globals body
  M.DPolicy policy -> validatePolicy globals policy
  M.DPolicyRaw expression -> validateExpr globals expression
  M.DOnError identifier -> requireValue globals (locatedSpan declaration) identifier
  _ -> []

validatePolicy :: Globals -> M.Policy -> [Diagnostic]
validatePolicy globals policy = case policy of
  M.PolicyClient expression -> validateExpr globals expression
  M.PolicyInsert expression -> validateExpr globals expression
  M.PolicyDelete expression -> validateExpr globals expression
  M.PolicyUpdate expression -> validateExpr globals expression
  M.PolicySequence expression -> validateExpr globals expression

validateType :: Globals -> M.Type -> [Diagnostic]
validateType globals typ = case locatedValue typ of
  M.TFun domain range -> validateType globals domain <> validateType globals range
  M.TRecord fields -> concatMap (validateType globals . snd) fields
  M.TDatatype identifier
    | Set.member identifier (globalDatatypes globals) -> []
    | otherwise -> [missing "datatype" (locatedSpan typ) identifier]
  M.TOption element -> validateType globals element
  M.TList element -> validateType globals element
  M.TSignal element -> validateType globals element
  _ -> []

validatePattern :: Globals -> M.Pattern -> [Diagnostic]
validatePattern globals pattern' = case locatedValue pattern' of
  M.PVar _ typ -> validateType globals typ
  M.PCon _ constructor nested ->
    validatePatCon globals (locatedSpan pattern') constructor <> maybe [] (validatePattern globals) nested
  M.PRecord fields -> concat
    [ validatePattern globals nested <> validateType globals typ
    | (_, nested, typ) <- fields
    ]
  M.PNone typ -> validateType globals typ
  M.PSome typ nested -> validateType globals typ <> validatePattern globals nested
  M.PPrim {} -> []

validatePatCon :: Globals -> Span -> M.PatCon -> [Diagnostic]
validatePatCon globals location constructor = case constructor of
  M.PConVar identifier
    | Set.member identifier (globalConstructors globals) -> []
    | otherwise -> [missing "datatype constructor" location identifier]
  M.PConFfi _ _ _ payload -> maybe [] (validateType globals) payload

validateStatic :: Globals -> M.StaticArg -> [Diagnostic]
validateStatic globals argument = case argument of
  M.StaticType typ -> validateType globals typ
  M.StaticRow fields -> concat
    [ validateStatic globals name <> validateStatic globals value
    | (name, value) <- fields
    ]
  M.StaticTuple elements -> concatMap (validateStatic globals) elements
  M.StaticFfi _ _ arguments -> concatMap (validateStatic globals) arguments
  M.StaticLambda body -> validateStatic globals body
  M.StaticApply function value -> validateStatic globals function <> validateStatic globals value
  M.StaticProject tuple _ -> validateStatic globals tuple
  M.StaticConcat left right -> validateStatic globals left <> validateStatic globals right
  _ -> []

validateExpr :: Globals -> M.Expr -> [Diagnostic]
validateExpr globals expression = case locatedValue expression of
  M.ENamed identifier -> requireValue globals (locatedSpan expression) identifier
  M.ECon _ constructor payload ->
    validatePatCon globals (locatedSpan expression) constructor <> maybe [] (validateExpr globals) payload
  M.ENone typ -> validateType globals typ
  M.ESome typ value -> validateType globals typ <> validateExpr globals value
  M.EFfi _ _ static -> concatMap (validateStatic globals) static
  M.EFfiApp _ _ static arguments ->
    concatMap (validateStatic globals) static
      <> concat [validateExpr globals value <> validateType globals typ | (value, typ) <- arguments]
  M.EApp function argument -> validateExpr globals function <> validateExpr globals argument
  M.EAbs _ domain range body -> validateType globals domain <> validateType globals range <> validateExpr globals body
  M.EStaticApp function argument -> validateExpr globals function <> validateStatic globals argument
  M.EUnop _ value -> validateExpr globals value
  M.EBinop _ _ left right -> validateExpr globals left <> validateExpr globals right
  M.ERecord fields -> concat
    [ validateStatic globals field <> validateExpr globals value <> validateType globals typ
    | (field, value, typ) <- fields
    ]
  M.EField record field -> validateExpr globals record <> validateStatic globals field
  M.ERecordConcat left right -> validateExpr globals left <> validateExpr globals right
  M.ERecordCut record fields -> validateExpr globals record <> concatMap (validateStatic globals) fields
  M.ECase scrutinee branches input result ->
    validateExpr globals scrutinee
      <> concat [validatePattern globals pattern' <> validateExpr globals body | (pattern', body) <- branches]
      <> validateType globals input
      <> validateType globals result
  M.EStrcat left right -> validateExpr globals left <> validateExpr globals right
  M.EError value typ -> validateExpr globals value <> validateType globals typ
  M.EReturnBlob content value typ -> maybe [] (validateExpr globals) content <> validateExpr globals value <> validateType globals typ
  M.ERedirect value typ -> validateExpr globals value <> validateType globals typ
  M.EWrite value -> validateExpr globals value
  M.ESeq first second -> validateExpr globals first <> validateExpr globals second
  M.ELet _ typ value body -> validateType globals typ <> validateExpr globals value <> validateExpr globals body
  M.EClosure identifier captures -> requireValue globals (locatedSpan expression) identifier <> concatMap (validateExpr globals) captures
  M.EQuery fields tables state query body initial ->
    concatMap (validateType globals . snd) fields
      <> concat [concatMap (validateType globals . snd) columns | (_, columns) <- tables]
      <> validateType globals state
      <> validateExpr globals query
      <> validateExpr globals body
      <> validateExpr globals initial
  M.EDml value _ -> validateExpr globals value
  M.ENextval value -> validateExpr globals value
  M.ESetval sequence' value -> validateExpr globals sequence' <> validateExpr globals value
  M.EUnurlify value typ _ -> validateExpr globals value <> validateType globals typ
  M.EJavaScript mode value -> validateJavaScriptMode globals mode <> validateExpr globals value
  M.ESignalReturn value -> validateExpr globals value
  M.ESignalBind signal continuation -> validateExpr globals signal <> validateExpr globals continuation
  M.ESignalSource value -> validateExpr globals value
  M.EServerCall call typ _ _ -> validateExpr globals call <> validateType globals typ
  M.ERecv channel typ -> validateExpr globals channel <> validateType globals typ
  M.ESleep value -> validateExpr globals value
  M.ESpawn value -> validateExpr globals value
  M.ESqlCache _ typ keys action ->
    validateType globals typ
      <> concatMap (validateExpr globals) keys
      <> validateExpr globals action
  M.ESqlCacheFlush typ flushes action ->
    validateType globals typ
      <> concat
      [ maybe [] (validateExpr globals) key
      | flush <- flushes
      , key <- M.sqlCacheFlushKeys flush
      ]
      <> validateExpr globals action
  M.EPrim {} -> []
  M.ERel {} -> []

validateJavaScriptMode :: Globals -> M.JavaScriptMode -> [Diagnostic]
validateJavaScriptMode globals mode = case mode of
  M.JavaScriptSource typ -> validateType globals typ
  _ -> []

requireValue :: Globals -> Span -> M.GlobalId -> [Diagnostic]
requireValue globals location identifier
  | Set.member identifier (globalValues globals) = []
  | otherwise = [missing "value" location identifier]

missing :: String -> Span -> M.GlobalId -> Diagnostic
missing description location identifier =
  diagnostic MonoPhase "missing-global" location
    ("Monomorphic " <> description <> " identity #" <> show (M.unGlobalId identifier) <> " has no declaration")
