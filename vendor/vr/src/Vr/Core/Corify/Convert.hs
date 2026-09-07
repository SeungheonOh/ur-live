-- | Location-preserving conversion of the non-module portions of Explicit
-- syntax.  Projections are resolved through the flattening environment built
-- by 'Vr.Core.Corify'.
module Vr.Core.Corify.Convert
  ( corifyKind
  , corifyCon
  , corifyPattern
  , corifyExpr
  , resolveFlat
  ) where

import qualified Vr.Core.Corify.State as S
import qualified Vr.Core.Syntax as C
import qualified Vr.Explicit.Syntax as E
import Vr.Source (Diagnostic, DiagnosticPhase (CorePhase), Located (..), diagnostic)

corifyKind :: E.Kind -> C.Kind
corifyKind source = Located (locatedSpan source) $ case locatedValue source of
  E.KType -> C.KType
  E.KArrow domain range -> C.KArrow (corifyKind domain) (corifyKind range)
  E.KName -> C.KName
  E.KRecord element -> C.KRecord (corifyKind element)
  E.KUnit -> C.KUnit
  E.KTuple elements -> C.KTuple (map corifyKind elements)
  E.KRel index -> C.KRel index
  E.KFun name body -> C.KFun name (corifyKind body)

corifyCon :: S.CorifyState -> E.Con -> Either Diagnostic C.Con
corifyCon state source = Located (locatedSpan source) <$> case locatedValue source of
  E.TFun domain range -> C.TFun <$> go domain <*> go range
  E.TCFun name kind body -> C.TCFun name (corifyKind kind) <$> go body
  E.TRecord row -> C.TRecord <$> go row
  E.CRel index -> pure (C.CRel index)
  E.CNamed identifier -> pure (C.CNamed (maybe identifier id (S.lookupConId identifier state)))
  E.CModProj identifier path name -> do
    flat <- resolveFlat state identifier path source
    case S.lookupConName name flat of
      Just (S.NormalCon target) -> pure (C.CNamed target)
      Just (S.ForeignCon moduleName)
        | moduleName == "Basis" && name == "unit" ->
            pure (C.TRecord (Located (locatedSpan source) (C.CRecord (Located (locatedSpan source) C.KType) [])))
        | otherwise -> pure (C.CFfi moduleName name)
      Nothing ->
        failure
          "unknown-constructor-projection"
          source
          ("Unknown constructor projection " <> dotted identifier path name <> " in " <> S.describeFlat flat)
  E.CApp function argument -> C.CApp <$> go function <*> go argument
  E.CAbs name kind body -> C.CAbs name (corifyKind kind) <$> go body
  E.CKAbs name body -> C.CKAbs name <$> go body
  E.CKApp function kind -> C.CKApp <$> go function <*> pure (corifyKind kind)
  E.TKFun name body -> C.TKFun name <$> go body
  E.CName name -> pure (C.CName name)
  E.CRecord kind fields -> C.CRecord (corifyKind kind) <$> mapM field fields
  E.CConcat left right -> C.CConcat <$> go left <*> go right
  E.CMap domain range -> pure (C.CMap (corifyKind domain) (corifyKind range))
  E.CUnit -> pure C.CUnit
  E.CTuple elements -> C.CTuple <$> mapM go elements
  E.CProj tuple index -> C.CProj <$> go tuple <*> pure index
  where
    go = corifyCon state
    field (name, value) = (,) <$> go name <*> go value

corifyPattern :: S.CorifyState -> E.Pattern -> Either Diagnostic C.Pattern
corifyPattern state source = Located (locatedSpan source) <$> case locatedValue source of
  E.PVar name typ -> C.PVar name <$> corifyCon state typ
  E.PPrim primitive -> pure (C.PPrim primitive)
  E.PCon classification constructor arguments nested ->
    C.PCon classification
      <$> corifyPatCon state source constructor
      <*> mapM (corifyCon state) arguments
      <*> traverse (corifyPattern state) nested
  E.PRecord fields -> C.PRecord <$> mapM field fields
  where
    field (name, nested, typ) =
      (,,) name <$> corifyPattern state nested <*> corifyCon state typ

corifyPatCon :: S.CorifyState -> E.Pattern -> E.PatCon -> Either Diagnostic C.PatCon
corifyPatCon state source constructor = case constructor of
  E.PConVar identifier -> case S.lookupConstructorId identifier state of
    Just target -> pure target
    Nothing -> failure "unknown-data-constructor" source "Unknown flattened data constructor"
  E.PConProj identifier path name -> do
    flat <- resolveFlat state identifier path source
    case S.lookupConstructorName name flat of
      Just target -> pure target
      Nothing -> failure "unknown-data-constructor-projection" source ("Unknown data constructor projection " <> dotted identifier path name)

corifyExpr :: S.CorifyState -> E.Expr -> Either Diagnostic C.Expr
corifyExpr state source = Located (locatedSpan source) <$> case locatedValue source of
  E.EPrim primitive -> pure (C.EPrim primitive)
  E.ERel index -> pure (C.ERel index)
  E.ENamed identifier -> case S.lookupValueId identifier state of
    Just (S.NormalValue target) -> pure (C.ENamed target)
    Just (S.ForeignValue moduleName name _) -> pure (C.EFfi moduleName name)
    Nothing -> pure (C.ENamed identifier)
  E.EModProj identifier path name -> corifyProjection state source identifier path name
  E.EApp function argument -> C.EApp <$> go function <*> go argument
  E.EAbs name domain range body ->
    C.EAbs name <$> con domain <*> con range <*> go body
  E.ECApp function argument -> C.ECApp <$> go function <*> con argument
  E.ECAbs name kind body -> C.ECAbs name (corifyKind kind) <$> go body
  E.EKAbs name body -> C.EKAbs name <$> go body
  E.EKApp function kind -> C.EKApp <$> go function <*> pure (corifyKind kind)
  E.ERecord fields -> C.ERecord <$> mapM recordField fields
  E.EField record name fieldType rest ->
    C.EField <$> go record <*> con name <*> con fieldType <*> con rest
  E.EConcat left leftRow right rightRow ->
    C.EConcat <$> go left <*> con leftRow <*> go right <*> con rightRow
  E.ECut record name fieldType rest ->
    C.ECut <$> go record <*> con name <*> con fieldType <*> con rest
  E.ECutMulti record fields rest -> C.ECutMulti <$> go record <*> con fields <*> con rest
  E.ECase scrutinee branches input result ->
    C.ECase <$> go scrutinee <*> mapM branch branches <*> con input <*> con result
  E.EWrite expression -> C.EWrite <$> go expression
  E.ELet name typ value body -> C.ELet name <$> con typ <*> go value <*> go body
  where
    go = corifyExpr state
    con = corifyCon state
    recordField (name, value, typ) = (,,) <$> con name <*> go value <*> con typ
    branch (pattern', body) = (,) <$> corifyPattern state pattern' <*> go body

corifyProjection
  :: S.CorifyState
  -> E.Expr
  -> E.GlobalId
  -> [String]
  -> String
  -> Either Diagnostic C.ExprF
corifyProjection state source identifier path name = do
  flat <- resolveFlat state identifier path source
  case S.lookupConstructorName name flat of
    Just constructor@C.PConFfi {} -> foreignConstructorValue source constructor
    _ -> case S.lookupValueName name flat of
      Just (S.NormalValue target) -> pure (C.ENamed target)
      Just (S.ForeignValue moduleName foreignName _) -> pure (C.EFfi moduleName foreignName)
      Nothing -> failure "unknown-value-projection" source ("Unknown value projection " <> dotted identifier path name)

foreignConstructorValue :: E.Expr -> C.PatCon -> Either Diagnostic C.ExprF
foreignConstructorValue source constructor@(C.PConFfi moduleName datatypeName parameters _ payload classification) =
  let at = locatedSpan source
      arguments = [Located at (C.CRel index) | index <- [0 .. length parameters - 1]]
      resultType = Located at (C.CFfi moduleName datatypeName)
      base = case payload of
        Nothing -> Located at (C.ECon classification constructor arguments Nothing)
        Just domain ->
          Located at
            (C.EAbs "x" domain resultType
              (Located at (C.ECon classification constructor arguments (Just (Located at (C.ERel 0))))))
      polymorphic = foldr (\parameter body -> Located at (C.ECAbs parameter (Located at C.KType) body)) base parameters
   in pure (locatedValue polymorphic)
foreignConstructorValue source _ = failure "foreign-constructor-shape" source "Expected a foreign data constructor"

resolveFlat
  :: S.CorifyState
  -> E.GlobalId
  -> [String]
  -> Located value
  -> Either Diagnostic S.Flat
resolveFlat state identifier path source = case S.lookupStructureId identifier state >>= (`S.projectPath` path) of
  Just flat -> pure flat
  Nothing -> failure "unknown-structure-projection" source ("Unknown structure projection rooted at #" <> show (E.unGlobalId identifier))

failure :: String -> Located value -> String -> Either Diagnostic result
failure code source message = Left (diagnostic CorePhase code (locatedSpan source) message)

dotted :: E.GlobalId -> [String] -> String -> String
dotted identifier path name = "#" <> show (E.unGlobalId identifier) <> "." <> concatMap (<> ".") path <> name
