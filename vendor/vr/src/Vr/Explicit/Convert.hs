-- | Evidence-erasing conversion from a solved, unnested elaboration tree to
-- the phase-distinct Explicit language.
module Vr.Explicit.Convert
  ( convertFile
  ) where

import qualified Vr.Elaborate.Syntax as A
import qualified Vr.Explicit.Syntax as E
import Vr.Source (Diagnostic, DiagnosticPhase (ExplicitPhase), Located (..), diagnostic)

convertFile :: A.File -> Either [Diagnostic] E.File
convertFile file = either (Left . pure) Right (fmap concat (mapM convertDecl file))

convertKind :: A.Kind -> Either Diagnostic E.Kind
convertKind source = Located (locatedSpan source) <$> case locatedValue source of
  A.KType -> pure E.KType
  A.KArrow domain range -> E.KArrow <$> convertKind domain <*> convertKind range
  A.KName -> pure E.KName
  A.KRecord element -> E.KRecord <$> convertKind element
  A.KUnit -> pure E.KUnit
  A.KTuple elements -> E.KTuple <$> mapM convertKind elements
  A.KRel index -> pure (E.KRel index)
  A.KFun name body -> E.KFun name <$> convertKind body
  A.KError -> failure "explicit-kind-error" source "Kind recovery node reached Explicit conversion"
  A.KMeta {} -> failure "explicit-kind-meta" source "Kind metavariable reached Explicit conversion"
  A.KTupleMeta {} -> failure "explicit-kind-meta" source "Tuple-kind metavariable reached Explicit conversion"

convertCon :: A.Con -> Either Diagnostic E.Con
convertCon source = case locatedValue source of
  A.TDisjoint _ _ body -> convertCon body
  value -> Located (locatedSpan source) <$> case value of
    A.TFun domain range -> E.TFun <$> convertCon domain <*> convertCon range
    A.TCFun _ name kind body -> E.TCFun name <$> convertKind kind <*> convertCon body
    A.TRecord row -> E.TRecord <$> convertCon row
    A.CRel index -> pure (E.CRel index)
    A.CNamed identifier -> pure (E.CNamed identifier)
    A.CModProj identifier path name -> pure (E.CModProj identifier path name)
    A.CApp function argument -> E.CApp <$> convertCon function <*> convertCon argument
    A.CAbs name kind body -> E.CAbs name <$> convertKind kind <*> convertCon body
    A.CKAbs name body -> E.CKAbs name <$> convertCon body
    A.CKApp function kind -> E.CKApp <$> convertCon function <*> convertKind kind
    A.TKFun name body -> E.TKFun name <$> convertCon body
    A.CName name -> pure (E.CName name)
    A.CRecord kind fields -> E.CRecord <$> convertKind kind <*> mapM convertConField fields
    A.CConcat left right -> E.CConcat <$> convertCon left <*> convertCon right
    A.CMap domain range -> E.CMap <$> convertKind domain <*> convertKind range
    A.CUnit -> pure E.CUnit
    A.CTuple elements -> E.CTuple <$> mapM convertCon elements
    A.CProj tuple index -> E.CProj <$> convertCon tuple <*> pure index
    A.CError -> failure "explicit-con-error" source "Constructor recovery node reached Explicit conversion"
    A.CMeta {} -> failure "explicit-con-meta" source "Constructor metavariable reached Explicit conversion"
  where
    convertConField (name, value) = (,) <$> convertCon name <*> convertCon value

convertPatCon :: A.PatCon -> E.PatCon
convertPatCon constructor = case constructor of
  A.PConVar identifier -> E.PConVar identifier
  A.PConProj identifier path name -> E.PConProj identifier path name

convertPattern :: A.Pattern -> Either Diagnostic E.Pattern
convertPattern source = Located (locatedSpan source) <$> case locatedValue source of
  A.PVar name typ -> E.PVar name <$> convertCon typ
  A.PPrim primitive -> pure (E.PPrim primitive)
  A.PCon classification constructor arguments nested ->
    E.PCon classification (convertPatCon constructor)
      <$> mapM convertCon arguments
      <*> traverse convertPattern nested
  A.PRecord fields _ -> E.PRecord <$> mapM convertPatternField fields
  where
    convertPatternField (name, nested, typ) =
      (,,) name <$> convertPattern nested <*> convertCon typ

convertExpr :: A.Expr -> Either Diagnostic E.Expr
convertExpr source = case locatedValue source of
  A.ELet declarations body result -> do
    body' <- convertExpr body
    result' <- convertCon result
    foldr (convertLocal result') (pure body') declarations
  value -> Located (locatedSpan source) <$> case value of
    A.EPrim primitive -> pure (E.EPrim primitive)
    A.ERel index -> pure (E.ERel index)
    A.ENamed identifier -> pure (E.ENamed identifier)
    A.EModProj identifier path name -> pure (E.EModProj identifier path name)
    A.EApp function argument -> E.EApp <$> convertExpr function <*> convertExpr argument
    A.EAbs name domain range body ->
      E.EAbs name <$> convertCon domain <*> convertCon range <*> convertExpr body
    A.ECApp function argument -> E.ECApp <$> convertExpr function <*> convertCon argument
    A.ECAbs _ name kind body -> E.ECAbs name <$> convertKind kind <*> convertExpr body
    A.EKAbs name body -> E.EKAbs name <$> convertExpr body
    A.EKApp function kind -> E.EKApp <$> convertExpr function <*> convertKind kind
    A.ERecord fields -> E.ERecord <$> mapM convertRecordField fields
    A.EField record name field rest ->
      E.EField <$> convertExpr record <*> convertCon name <*> convertCon field <*> convertCon rest
    A.EConcat left leftRow right rightRow ->
      E.EConcat <$> convertExpr left <*> convertCon leftRow <*> convertExpr right <*> convertCon rightRow
    A.ECut record name field rest ->
      E.ECut <$> convertExpr record <*> convertCon name <*> convertCon field <*> convertCon rest
    A.ECutMulti record fields rest ->
      E.ECutMulti <$> convertExpr record <*> convertCon fields <*> convertCon rest
    A.ECase scrutinee branches input result ->
      E.ECase <$> convertExpr scrutinee <*> mapM convertBranch branches <*> convertCon input <*> convertCon result
    A.EError -> failure "explicit-expression-error" source "Expression recovery node reached Explicit conversion"
    A.EMeta {} -> failure "explicit-expression-meta" source "Expression metavariable reached Explicit conversion"
  where
    convertRecordField (name, value, typ) =
      (,,) <$> convertCon name <*> convertExpr value <*> convertCon typ
    convertBranch (pattern', body) = (,) <$> convertPattern pattern' <*> convertExpr body
    convertLocal result declaration bodyResult = case locatedValue declaration of
      A.EDVal pattern' typ value -> do
        pattern'' <- convertPattern pattern'
        typ' <- convertCon typ
        value' <- convertExpr value
        body' <- bodyResult
        pure $ case locatedValue pattern'' of
          E.PVar name _ -> Located (locatedSpan declaration) (E.ELet name typ' value' body')
          _ -> Located (locatedSpan declaration) (E.ECase value' [(pattern'', body')] typ' result)
      A.EDValRec {} ->
        failure "explicit-local-recursion" declaration "Local recursive declaration remains after Unnest"

convertSignature :: A.Signature -> Either Diagnostic E.Signature
convertSignature source = Located (locatedSpan source) <$> case locatedValue source of
  A.SgnConst items -> E.SgnConst . concat <$> mapM convertSigItem items
  A.SgnVar identifier -> pure (E.SgnVar identifier)
  A.SgnFun name identifier domain range ->
    E.SgnFun name identifier <$> convertSignature domain <*> convertSignature range
  A.SgnWhere base path name definition ->
    E.SgnWhere <$> convertSignature base <*> pure path <*> pure name <*> convertCon definition
  A.SgnProj identifier path name -> pure (E.SgnProj identifier path name)
  A.SgnError -> failure "explicit-signature-error" source "Signature recovery node reached Explicit conversion"

convertSigItem :: A.SigItem -> Either Diagnostic [E.SigItem]
convertSigItem source = fmap (maybe [] (pure . Located (locatedSpan source))) $ case locatedValue source of
  A.SgiConAbs name identifier kind -> Just . E.SgiConAbs name identifier <$> convertKind kind
  A.SgiCon name identifier kind definition ->
    fmap Just (E.SgiCon name identifier <$> convertKind kind <*> convertCon definition)
  A.SgiDatatype definitions -> Just . E.SgiDatatype <$> mapM convertDatatype definitions
  A.SgiDatatypeImp name identifier original path originalName parameters constructors ->
    Just . E.SgiDatatypeImp name identifier original path originalName parameters
      <$> mapM convertDatatypeConstructor constructors
  A.SgiVal name identifier typ -> Just . E.SgiVal name identifier <$> convertCon typ
  A.SgiStr _ name identifier signature -> Just . E.SgiStr name identifier <$> convertSignature signature
  A.SgiSgn name identifier signature -> Just . E.SgiSgn name identifier <$> convertSignature signature
  A.SgiConstraint {} -> pure Nothing
  A.SgiClassAbs name identifier kind -> do
    kind' <- convertKind kind
    let classKind = Located (locatedSpan kind') (E.KArrow kind' (Located (locatedSpan kind') E.KType))
    pure (Just (E.SgiConAbs name identifier classKind))
  A.SgiClass name identifier kind definition -> do
    kind' <- convertKind kind
    definition' <- convertCon definition
    let classKind = Located (locatedSpan kind') (E.KArrow kind' (Located (locatedSpan kind') E.KType))
    pure (Just (E.SgiCon name identifier classKind definition'))

convertDecl :: A.Decl -> Either Diagnostic [E.Decl]
convertDecl source = fmap (maybe [] (pure . Located (locatedSpan source))) $ case locatedValue source of
  A.DCon name identifier kind definition ->
    fmap Just (E.DCon name identifier <$> convertKind kind <*> convertCon definition)
  A.DDatatype definitions -> Just . E.DDatatype <$> mapM convertDatatype definitions
  A.DDatatypeImp name identifier original path originalName parameters constructors ->
    Just . E.DDatatypeImp name identifier original path originalName parameters
      <$> mapM convertDatatypeConstructor constructors
  A.DVal name identifier typ expression ->
    fmap Just (E.DVal name identifier <$> convertCon typ <*> convertExpr expression)
  A.DValRec bindings -> Just . E.DValRec <$> mapM convertRecursiveBinding bindings
  A.DSgn name identifier signature -> Just . E.DSgn name identifier <$> convertSignature signature
  A.DStr name identifier signature structure ->
    fmap Just (E.DStr name identifier <$> convertSignature signature <*> convertStructure structure)
  A.DFfiStr name identifier signature -> Just . E.DFfiStr name identifier <$> convertSignature signature
  A.DConstraint {} -> pure Nothing
  A.DExport identifier signature structure ->
    fmap Just (E.DExport identifier <$> convertSignature signature <*> convertStructure structure)
  A.DTable basis name identifier row primary keys constraints uniques ->
    fmap Just
      ( E.DTable basis name identifier
          <$> convertCon row <*> convertExpr primary <*> convertCon keys
          <*> convertExpr constraints <*> convertCon uniques
      )
  A.DSequence basis name identifier -> pure (Just (E.DSequence basis name identifier))
  A.DView basis name identifier expression row ->
    fmap Just (E.DView basis name identifier <$> convertExpr expression <*> convertCon row)
  A.DIndex table modes -> fmap Just (E.DIndex <$> convertExpr table <*> convertExpr modes)
  A.DDatabase database -> pure (Just (E.DDatabase database))
  A.DCookie basis name identifier typ -> Just . E.DCookie basis name identifier <$> convertCon typ
  A.DStyle basis name identifier -> pure (Just (E.DStyle basis name identifier))
  A.DTask kind body -> fmap Just (E.DTask <$> convertExpr kind <*> convertExpr body)
  A.DPolicy expression -> Just . E.DPolicy <$> convertExpr expression
  A.DOnError identifier path name -> pure (Just (E.DOnError identifier path name))
  A.DFfi name identifier modes typ -> Just . E.DFfi name identifier modes <$> convertCon typ
  where
    convertRecursiveBinding (name, identifier, typ, expression) =
      (,,,) name identifier <$> convertCon typ <*> convertExpr expression

convertStructure :: A.Structure -> Either Diagnostic E.Structure
convertStructure source = Located (locatedSpan source) <$> case locatedValue source of
  A.StrConst declarations -> E.StrConst . concat <$> mapM convertDecl declarations
  A.StrVar identifier -> pure (E.StrVar identifier)
  A.StrProj base name -> E.StrProj <$> convertStructure base <*> pure name
  A.StrFun name identifier domain range body ->
    E.StrFun name identifier <$> convertSignature domain <*> convertSignature range <*> convertStructure body
  A.StrApp function argument -> E.StrApp <$> convertStructure function <*> convertStructure argument
  A.StrError -> failure "explicit-structure-error" source "Structure recovery node reached Explicit conversion"

convertDatatype
  :: (String, A.GlobalId, [String], [(String, A.GlobalId, Maybe A.Con)])
  -> Either Diagnostic (String, E.GlobalId, [String], [(String, E.GlobalId, Maybe E.Con)])
convertDatatype (name, identifier, parameters, constructors) =
  (,,,) name identifier parameters <$> mapM convertDatatypeConstructor constructors

convertDatatypeConstructor
  :: (String, A.GlobalId, Maybe A.Con)
  -> Either Diagnostic (String, E.GlobalId, Maybe E.Con)
convertDatatypeConstructor (name, identifier, payload) =
  (,,) name identifier <$> traverse convertCon payload

failure :: String -> Located value -> String -> Either Diagnostic result
failure code source message =
  Left (diagnostic ExplicitPhase code (locatedSpan source) message)
