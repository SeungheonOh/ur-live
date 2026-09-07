-- | Successful frontend finalization: reject unresolved inference state and
-- materialize every solution into the immutable backend-neutral tree.
module Vr.Elaborate.Finalize
  ( zonkFile
  , zonkSignature
  , validateResolvedFile
  ) where

import Control.Monad (when)
import Control.Monad.State.Strict (gets)
import Vr.Elaborate.State
import Vr.Elaborate.Syntax
import Vr.Elaborate.Types
import Vr.Source (Located (..))
-- | Materialize all inference solutions into the backend-neutral tree.  The
-- solver deliberately keeps substitutions in 'ElabState' while reaching its
-- fixed point; no backend should need access to that mutable representation.
zonkFile :: File -> ElabM File
zonkFile = mapM zonkDeclaration

zonkDeclaration :: Decl -> ElabM Decl
zonkDeclaration declaration = do
  value <- case locatedValue declaration of
    DCon name identifier kind constructor ->
      DCon name identifier <$> zonkKind kind <*> zonkCon constructor
    DDatatype definitions -> DDatatype <$> mapM zonkDatatypeDefinition definitions
    DDatatypeImp name identifier original path originalName parameters constructors ->
      DDatatypeImp name identifier original path originalName parameters <$> mapM zonkDatatypeConstructor constructors
    DVal name identifier typ expression ->
      DVal name identifier <$> zonkCon typ <*> zonkExpression expression
    DValRec bindings -> DValRec <$> mapM zonkRecursiveBinding bindings
    DSgn name identifier signature -> DSgn name identifier <$> zonkSignature signature
    DStr name identifier signature structure ->
      DStr name identifier <$> zonkSignature signature <*> zonkStructure structure
    DFfiStr name identifier signature -> DFfiStr name identifier <$> zonkSignature signature
    DConstraint left right -> DConstraint <$> zonkCon left <*> zonkCon right
    DExport identifier signature structure ->
      DExport identifier <$> zonkSignature signature <*> zonkStructure structure
    DTable tableId name valueId row primary keys constraints uniques ->
      DTable tableId name valueId
        <$> zonkCon row
        <*> zonkExpression primary
        <*> zonkCon keys
        <*> zonkExpression constraints
        <*> zonkCon uniques
    DSequence tableId name valueId -> pure (DSequence tableId name valueId)
    DView tableId name valueId expression typ ->
      DView tableId name valueId <$> zonkExpression expression <*> zonkCon typ
    DIndex first second -> DIndex <$> zonkExpression first <*> zonkExpression second
    DDatabase database -> pure (DDatabase database)
    DCookie cookieId name valueId typ -> DCookie cookieId name valueId <$> zonkCon typ
    DStyle styleId name valueId -> pure (DStyle styleId name valueId)
    DTask kind expression -> DTask <$> zonkExpression kind <*> zonkExpression expression
    DPolicy expression -> DPolicy <$> zonkExpression expression
    DOnError identifier path name -> pure (DOnError identifier path name)
    DFfi name identifier modes typ -> DFfi name identifier modes <$> zonkCon typ
  pure declaration {locatedValue = value}
  where
    zonkRecursiveBinding (name, identifier, typ, expression) =
      (,,,) name identifier <$> zonkCon typ <*> zonkExpression expression

zonkDatatypeDefinition
  :: (String, GlobalId, [String], [(String, GlobalId, Maybe Con)])
  -> ElabM (String, GlobalId, [String], [(String, GlobalId, Maybe Con)])
zonkDatatypeDefinition (name, identifier, parameters, constructors) =
  (,,,) name identifier parameters <$> mapM zonkDatatypeConstructor constructors

zonkDatatypeConstructor
  :: (String, GlobalId, Maybe Con)
  -> ElabM (String, GlobalId, Maybe Con)
zonkDatatypeConstructor (name, identifier, argument) =
  (,,) name identifier <$> traverse zonkCon argument

zonkSignature :: Signature -> ElabM Signature
zonkSignature signature = do
  value <- case locatedValue signature of
    SgnConst items -> SgnConst <$> mapM zonkSignatureItem items
    SgnVar identifier -> pure (SgnVar identifier)
    SgnFun name identifier domain range ->
      SgnFun name identifier <$> zonkSignature domain <*> zonkSignature range
    SgnWhere base path name definition ->
      SgnWhere <$> zonkSignature base <*> pure path <*> pure name <*> zonkCon definition
    SgnProj identifier path name -> pure (SgnProj identifier path name)
    SgnError -> pure SgnError
  pure signature {locatedValue = value}

zonkSignatureItem :: SigItem -> ElabM SigItem
zonkSignatureItem item = do
  value <- case locatedValue item of
    SgiConAbs name identifier kind -> SgiConAbs name identifier <$> zonkKind kind
    SgiCon name identifier kind definition ->
      SgiCon name identifier <$> zonkKind kind <*> zonkCon definition
    SgiDatatype definitions -> SgiDatatype <$> mapM zonkDatatypeDefinition definitions
    SgiDatatypeImp name identifier original path originalName parameters constructors ->
      SgiDatatypeImp name identifier original path originalName parameters <$> mapM zonkDatatypeConstructor constructors
    SgiVal name identifier typ -> SgiVal name identifier <$> zonkCon typ
    SgiStr mode name identifier signature -> SgiStr mode name identifier <$> zonkSignature signature
    SgiSgn name identifier signature -> SgiSgn name identifier <$> zonkSignature signature
    SgiConstraint left right -> SgiConstraint <$> zonkCon left <*> zonkCon right
    SgiClassAbs name identifier kind -> SgiClassAbs name identifier <$> zonkKind kind
    SgiClass name identifier kind definition ->
      SgiClass name identifier <$> zonkKind kind <*> zonkCon definition
  pure item {locatedValue = value}

zonkStructure :: Structure -> ElabM Structure
zonkStructure structure = do
  value <- case locatedValue structure of
    StrConst declarations -> StrConst <$> mapM zonkDeclaration declarations
    StrVar identifier -> pure (StrVar identifier)
    StrProj base name -> StrProj <$> zonkStructure base <*> pure name
    StrFun name identifier domain range body ->
      StrFun name identifier <$> zonkSignature domain <*> zonkSignature range <*> zonkStructure body
    StrApp function argument -> StrApp <$> zonkStructure function <*> zonkStructure argument
    StrError -> pure StrError
  pure structure {locatedValue = value}

zonkPattern :: Pattern -> ElabM Pattern
zonkPattern pattern' = do
  value <- case locatedValue pattern' of
    PVar name typ -> PVar name <$> zonkCon typ
    PPrim primitive -> pure (PPrim primitive)
    PCon classification constructor arguments nested ->
      PCon classification constructor <$> mapM zonkCon arguments <*> traverse zonkPattern nested
    PRecord fields flexible -> PRecord <$> mapM zonkField fields <*> pure flexible
  pure pattern' {locatedValue = value}
  where
    zonkField (name, nested, typ) = (,,) name <$> zonkPattern nested <*> zonkCon typ

zonkExpression :: Expr -> ElabM Expr
zonkExpression expression = do
  value <- case locatedValue expression of
    EPrim primitive -> pure (EPrim primitive)
    ERel index -> pure (ERel index)
    ENamed identifier -> pure (ENamed identifier)
    EModProj identifier path name -> pure (EModProj identifier path name)
    EApp function argument -> EApp <$> zonkExpression function <*> zonkExpression argument
    EAbs name domain range body ->
      EAbs name <$> zonkCon domain <*> zonkCon range <*> zonkExpression body
    ECApp function argument -> ECApp <$> zonkExpression function <*> zonkCon argument
    ECAbs explicitness name kind body ->
      ECAbs explicitness name <$> zonkKind kind <*> zonkExpression body
    EKAbs name body -> EKAbs name <$> zonkExpression body
    EKApp function kind -> EKApp <$> zonkExpression function <*> zonkKind kind
    ERecord fields -> ERecord <$> mapM zonkRecordField fields
    EField record name fieldType rest ->
      EField <$> zonkExpression record <*> zonkCon name <*> zonkCon fieldType <*> zonkCon rest
    EConcat left leftRow right rightRow ->
      EConcat <$> zonkExpression left <*> zonkCon leftRow <*> zonkExpression right <*> zonkCon rightRow
    ECut record field fieldType rest ->
      ECut <$> zonkExpression record <*> zonkCon field <*> zonkCon fieldType <*> zonkCon rest
    ECutMulti record fields rest ->
      ECutMulti <$> zonkExpression record <*> zonkCon fields <*> zonkCon rest
    ECase scrutinee branches input result ->
      ECase <$> zonkExpression scrutinee <*> mapM zonkBranch branches <*> zonkCon input <*> zonkCon result
    EError -> pure EError
    EMeta identifier -> do
      solution <- readExprMeta identifier
      case solution of
        Nothing -> pure (EMeta identifier)
        Just solved -> locatedValue <$> zonkExpression solved
    ELet declarations body typ ->
      ELet <$> mapM zonkExpressionDeclaration declarations <*> zonkExpression body <*> zonkCon typ
  pure expression {locatedValue = value}
  where
    zonkRecordField (name, field, typ) =
      (,,) <$> zonkCon name <*> zonkExpression field <*> zonkCon typ
    zonkBranch (pattern', branch) = (,) <$> zonkPattern pattern' <*> zonkExpression branch

zonkExpressionDeclaration :: EDecl -> ElabM EDecl
zonkExpressionDeclaration declaration = do
  value <- case locatedValue declaration of
    EDVal pattern' typ expression ->
      EDVal <$> zonkPattern pattern' <*> zonkCon typ <*> zonkExpression expression
    EDValRec bindings -> EDValRec <$> mapM zonkBinding bindings
  pure declaration {locatedValue = value}
  where
    zonkBinding (name, typ, expression) =
      (,,) name <$> zonkCon typ <*> zonkExpression expression
-- The reference elaborator rejects a file if its fixed point still leaves a
-- kind or constructor unification variable in the elaborated tree.  This is a
-- file-level check: variables created only during a failed speculative search
-- do not count, while variables buried in expressions, signatures, or nested
-- structures do.
validateResolvedFile :: File -> ElabM ()
validateResolvedFile file = do
  priorProblems <- gets elaborationDiagnosticsRev
  when (null priorProblems) $ do
    let declarations = concatMap nestedDeclarationsFirst file
    kindFailure <- firstDeclarationWith declarationHasUnresolvedKind declarations
    case kindFailure of
      Just declaration ->
        withSpanError
          "undetermined-kind"
          (locatedSpan declaration)
          "Some kind unification variables are undetermined in declaration"
      Nothing -> do
        conFailure <- firstDeclarationWith declarationHasUnresolvedCon declarations
        case conFailure of
          Just declaration ->
            withSpanError
              "undetermined-constructor"
              (locatedSpan declaration)
              "Some constructor unification variables are undetermined in declaration"
          Nothing -> do
            expressionFailure <- firstDeclarationWith declarationHasUnresolvedExpression declarations
            case expressionFailure of
              Just declaration ->
                withSpanError
                  "undetermined-expression"
                  (locatedSpan declaration)
                  "Some implicit expressions are undetermined in declaration"
              Nothing -> do
                recoveryFailure <- firstDeclarationWith (pure . declarationContainsRecovery) declarations
                case recoveryFailure of
                  Just declaration ->
                    withSpanError
                      "unresolved-recovery-node"
                      (locatedSpan declaration)
                      "A recovery/error node remains in declaration"
                  Nothing -> pure ()

nestedDeclarationsFirst :: Decl -> [Decl]
nestedDeclarationsFirst declaration = nested <> [declaration]
  where
    nested = case locatedValue declaration of
      DStr _ _ _ structure -> structureDeclarations structure
      DExport _ _ structure -> structureDeclarations structure
      _ -> []

structureDeclarations :: Structure -> [Decl]
structureDeclarations structure = case locatedValue structure of
  StrConst declarations -> concatMap nestedDeclarationsFirst declarations
  StrProj base _ -> structureDeclarations base
  StrFun _ _ _ _ body -> structureDeclarations body
  StrApp function argument -> structureDeclarations function <> structureDeclarations argument
  _ -> []

firstDeclarationWith :: (Decl -> ElabM Bool) -> [Decl] -> ElabM (Maybe Decl)
firstDeclarationWith _ [] = pure Nothing
firstDeclarationWith predicate (declaration : rest) = do
  found <- predicate declaration
  if found then pure (Just declaration) else firstDeclarationWith predicate rest

declarationHasUnresolvedKind :: Decl -> ElabM Bool
declarationHasUnresolvedKind declaration = do
  let (directKinds, constructors) = declarationRoots declaration
  direct <- anyMElab kindHasUnresolved directKinds
  if direct then pure True else anyMElab conHasUnresolvedKind constructors

declarationHasUnresolvedCon :: Decl -> ElabM Bool
declarationHasUnresolvedCon declaration =
  anyMElab conHasUnresolved (snd (declarationRoots declaration))

declarationHasUnresolvedExpression :: Decl -> ElabM Bool
declarationHasUnresolvedExpression declaration = do
  expressions <- mapM zonkExpression (declarationExpressionRoots declaration)
  pure (any expressionContainsMeta expressions)

declarationExpressionRoots :: Decl -> [Expr]
declarationExpressionRoots declaration = case locatedValue declaration of
  DVal _ _ _ expression -> [expression]
  DValRec bindings -> [expression | (_, _, _, expression) <- bindings]
  DTable _ _ _ _ primary _ constraints _ -> [primary, constraints]
  DView _ _ _ expression _ -> [expression]
  DIndex first second -> [first, second]
  DTask kind expression -> [kind, expression]
  DPolicy expression -> [expression]
  _ -> []

expressionContainsMeta :: Expr -> Bool
expressionContainsMeta expression = case locatedValue expression of
  EApp function argument -> any expressionContainsMeta [function, argument]
  EAbs _ _ _ body -> expressionContainsMeta body
  ECApp function _ -> expressionContainsMeta function
  ECAbs _ _ _ body -> expressionContainsMeta body
  EKAbs _ body -> expressionContainsMeta body
  EKApp function _ -> expressionContainsMeta function
  ERecord fields -> any (expressionContainsMeta . recordValue) fields
  EField record _ _ _ -> expressionContainsMeta record
  EConcat left _ right _ -> any expressionContainsMeta [left, right]
  ECut record _ _ _ -> expressionContainsMeta record
  ECutMulti record _ _ -> expressionContainsMeta record
  ECase scrutinee branches _ _ ->
    expressionContainsMeta scrutinee || any (expressionContainsMeta . snd) branches
  EMeta {} -> True
  ELet declarations body _ ->
    any expressionDeclarationContainsMeta declarations || expressionContainsMeta body
  _ -> False
  where
    recordValue (_, value, _) = value

expressionDeclarationContainsMeta :: EDecl -> Bool
expressionDeclarationContainsMeta declaration = case locatedValue declaration of
  EDVal _ _ expression -> expressionContainsMeta expression
  EDValRec bindings -> any (expressionContainsMeta . bindingExpression) bindings
  where
    bindingExpression (_, _, expression) = expression

-- Error nodes are useful while elaboration is recovering from an earlier
-- diagnostic, but they are not part of the backend contract.  Keep this
-- traversal independent of metavariable validation: a fully solved tree may
-- still contain a recovery sentinel introduced by a forgotten lowering case.
declarationContainsRecovery :: Decl -> Bool
declarationContainsRecovery declaration = case locatedValue declaration of
  DCon _ _ kind constructor -> kindContainsRecovery kind || conContainsRecovery constructor
  DDatatype definitions -> any datatypeDefinitionContainsRecovery definitions
  DDatatypeImp _ _ _ _ _ _ constructors -> any datatypeConstructorContainsRecovery constructors
  DVal _ _ typ expression -> conContainsRecovery typ || expressionContainsRecovery expression
  DValRec bindings -> any recursiveBindingContainsRecovery bindings
  DSgn _ _ signature -> signatureContainsRecovery signature
  DStr _ _ signature structure -> signatureContainsRecovery signature || structureContainsRecovery structure
  DFfiStr _ _ signature -> signatureContainsRecovery signature
  DConstraint left right -> any conContainsRecovery [left, right]
  DExport _ signature structure -> signatureContainsRecovery signature || structureContainsRecovery structure
  DTable _ _ _ row primary keys constraints uniques ->
    any conContainsRecovery [row, keys, uniques]
      || any expressionContainsRecovery [primary, constraints]
  DSequence {} -> False
  DView _ _ _ expression typ -> expressionContainsRecovery expression || conContainsRecovery typ
  DIndex table modes -> any expressionContainsRecovery [table, modes]
  DDatabase {} -> False
  DCookie _ _ _ typ -> conContainsRecovery typ
  DStyle {} -> False
  DTask kind expression -> any expressionContainsRecovery [kind, expression]
  DPolicy expression -> expressionContainsRecovery expression
  DOnError {} -> False
  DFfi _ _ _ typ -> conContainsRecovery typ
  where
    recursiveBindingContainsRecovery (_, _, typ, expression) =
      conContainsRecovery typ || expressionContainsRecovery expression

datatypeDefinitionContainsRecovery
  :: (String, GlobalId, [String], [(String, GlobalId, Maybe Con)])
  -> Bool
datatypeDefinitionContainsRecovery (_, _, _, constructors) =
  any datatypeConstructorContainsRecovery constructors

datatypeConstructorContainsRecovery :: (String, GlobalId, Maybe Con) -> Bool
datatypeConstructorContainsRecovery (_, _, payload) = maybe False conContainsRecovery payload

signatureContainsRecovery :: Signature -> Bool
signatureContainsRecovery signature = case locatedValue signature of
  SgnConst items -> any signatureItemContainsRecovery items
  SgnVar {} -> False
  SgnFun _ _ domain range -> any signatureContainsRecovery [domain, range]
  SgnWhere base _ _ definition -> signatureContainsRecovery base || conContainsRecovery definition
  SgnProj {} -> False
  SgnError -> True

signatureItemContainsRecovery :: SigItem -> Bool
signatureItemContainsRecovery item = case locatedValue item of
  SgiConAbs _ _ kind -> kindContainsRecovery kind
  SgiCon _ _ kind definition -> kindContainsRecovery kind || conContainsRecovery definition
  SgiDatatype definitions -> any datatypeDefinitionContainsRecovery definitions
  SgiDatatypeImp _ _ _ _ _ _ constructors -> any datatypeConstructorContainsRecovery constructors
  SgiVal _ _ typ -> conContainsRecovery typ
  SgiStr _ _ _ signature -> signatureContainsRecovery signature
  SgiSgn _ _ signature -> signatureContainsRecovery signature
  SgiConstraint left right -> any conContainsRecovery [left, right]
  SgiClassAbs _ _ kind -> kindContainsRecovery kind
  SgiClass _ _ kind definition -> kindContainsRecovery kind || conContainsRecovery definition

structureContainsRecovery :: Structure -> Bool
structureContainsRecovery structure = case locatedValue structure of
  StrConst declarations -> any declarationContainsRecovery declarations
  StrVar {} -> False
  StrProj base _ -> structureContainsRecovery base
  StrFun _ _ domain range body ->
    any signatureContainsRecovery [domain, range] || structureContainsRecovery body
  StrApp function argument -> any structureContainsRecovery [function, argument]
  StrError -> True

kindContainsRecovery :: Kind -> Bool
kindContainsRecovery kind = case locatedValue kind of
  KArrow domain range -> any kindContainsRecovery [domain, range]
  KRecord element -> kindContainsRecovery element
  KTuple elements -> any kindContainsRecovery elements
  KError -> True
  KTupleMeta _ _ observations -> any (kindContainsRecovery . snd) observations
  KFun _ body -> kindContainsRecovery body
  _ -> False

conContainsRecovery :: Con -> Bool
conContainsRecovery constructor = case locatedValue constructor of
  TFun domain range -> any conContainsRecovery [domain, range]
  TCFun _ _ kind body -> kindContainsRecovery kind || conContainsRecovery body
  TRecord row -> conContainsRecovery row
  TDisjoint left right body -> any conContainsRecovery [left, right, body]
  CApp function argument -> any conContainsRecovery [function, argument]
  CAbs _ kind body -> kindContainsRecovery kind || conContainsRecovery body
  CKAbs _ body -> conContainsRecovery body
  CKApp function kind -> conContainsRecovery function || kindContainsRecovery kind
  TKFun _ body -> conContainsRecovery body
  CRecord kind fields ->
    kindContainsRecovery kind
      || any (\(name, value) -> any conContainsRecovery [name, value]) fields
  CConcat left right -> any conContainsRecovery [left, right]
  CMap domain range -> any kindContainsRecovery [domain, range]
  CTuple elements -> any conContainsRecovery elements
  CProj tuple _ -> conContainsRecovery tuple
  CError -> True
  CMeta _ _ kind _ -> kindContainsRecovery kind
  _ -> False

patternContainsRecovery :: Pattern -> Bool
patternContainsRecovery pattern' = case locatedValue pattern' of
  PVar _ typ -> conContainsRecovery typ
  PPrim {} -> False
  PCon _ _ arguments nested ->
    any conContainsRecovery arguments || maybe False patternContainsRecovery nested
  PRecord fields _ -> any fieldContainsRecovery fields
  where
    fieldContainsRecovery (_, nested, typ) =
      patternContainsRecovery nested || conContainsRecovery typ

expressionContainsRecovery :: Expr -> Bool
expressionContainsRecovery expression = case locatedValue expression of
  EPrim {} -> False
  ERel {} -> False
  ENamed {} -> False
  EModProj {} -> False
  EApp function argument -> any expressionContainsRecovery [function, argument]
  EAbs _ domain range body ->
    any conContainsRecovery [domain, range] || expressionContainsRecovery body
  ECApp function argument -> expressionContainsRecovery function || conContainsRecovery argument
  ECAbs _ _ kind body -> kindContainsRecovery kind || expressionContainsRecovery body
  EKAbs _ body -> expressionContainsRecovery body
  EKApp function kind -> expressionContainsRecovery function || kindContainsRecovery kind
  ERecord fields -> any recordFieldContainsRecovery fields
  EField record name fieldType rest ->
    expressionContainsRecovery record || any conContainsRecovery [name, fieldType, rest]
  EConcat left leftRow right rightRow ->
    any expressionContainsRecovery [left, right] || any conContainsRecovery [leftRow, rightRow]
  ECut record field fieldType rest ->
    expressionContainsRecovery record || any conContainsRecovery [field, fieldType, rest]
  ECutMulti record fields rest ->
    expressionContainsRecovery record || any conContainsRecovery [fields, rest]
  ECase scrutinee branches input result ->
    expressionContainsRecovery scrutinee
      || any branchContainsRecovery branches
      || any conContainsRecovery [input, result]
  EError -> True
  EMeta {} -> False
  ELet declarations body typ ->
    any expressionDeclarationContainsRecovery declarations
      || expressionContainsRecovery body
      || conContainsRecovery typ
  where
    recordFieldContainsRecovery (name, value, typ) =
      any conContainsRecovery [name, typ] || expressionContainsRecovery value
    branchContainsRecovery (pattern', branch) =
      patternContainsRecovery pattern' || expressionContainsRecovery branch

expressionDeclarationContainsRecovery :: EDecl -> Bool
expressionDeclarationContainsRecovery declaration = case locatedValue declaration of
  EDVal pattern' typ expression ->
    patternContainsRecovery pattern' || conContainsRecovery typ || expressionContainsRecovery expression
  EDValRec bindings -> any bindingContainsRecovery bindings
  where
    bindingContainsRecovery (_, typ, expression) =
      conContainsRecovery typ || expressionContainsRecovery expression

kindHasUnresolved :: Kind -> ElabM Bool
kindHasUnresolved kind0 = do
  kind <- zonkKind kind0
  pure (go kind)
  where
    go kind = case locatedValue kind of
      KMeta {} -> True
      KTupleMeta {} -> True
      KArrow domain range -> go domain || go range
      KRecord element -> go element
      KTuple elements -> any go elements
      KFun _ body -> go body
      _ -> False

-- Inspect embedded kinds without materializing an entire replacement
-- constructor tree just to discard it. Follow solved
-- metas at their use-site depth; unresolved metas retain their annotated kind.
conHasUnresolvedKind :: Con -> ElabM Bool
conHasUnresolvedKind constructor = case locatedValue constructor of
  CMeta identifier level kind _ -> do
    solution <- readConMeta identifier
    maybe (kindHasUnresolved kind) (go . liftCon 0 level) solution
  TFun domain range -> descend [domain, range]
  TCFun _ _ kind body -> withKinds [kind] [body]
  TRecord row -> go row
  TDisjoint left right body -> descend [left, right, body]
  CApp function argument -> descend [function, argument]
  CAbs _ kind body -> withKinds [kind] [body]
  CKAbs _ body -> go body
  CKApp function kind -> withKinds [kind] [function]
  TKFun _ body -> go body
  CRecord kind fields -> withKinds [kind] (concatMap (\(name, value) -> [name, value]) fields)
  CConcat left right -> descend [left, right]
  CMap domain range -> anyMElab kindHasUnresolved [domain, range]
  CTuple elements -> descend elements
  CProj tuple _ -> go tuple
  _ -> pure False
  where
    go = conHasUnresolvedKind
    descend = anyMElab go
    withKinds kinds children = do
      unresolved <- anyMElab kindHasUnresolved kinds
      if unresolved then pure True else descend children

conHasUnresolved :: Con -> ElabM Bool
conHasUnresolved constructor =
  -- This pass only needs to resolve the current head. Descendants are checked
  -- in their original order, including any unit-kind defaults written by an
  -- earlier sibling. Re-zonking the entire subtree at every node is quadratic.
  case locatedValue constructor of
    CMeta identifier level kind _ -> do
      solution <- readConMeta identifier
      case solution of
        Just value -> conHasUnresolved (liftCon 0 level value)
        Nothing -> do
          kind' <- zonkKind kind
          case locatedValue kind' of
            KUnit -> writeConMeta identifier (Located (locatedSpan constructor) CUnit) >> pure False
            _ -> pure True
    TFun domain range -> anyMElab conHasUnresolved [domain, range]
    TCFun _ _ _ body -> conHasUnresolved body
    TRecord row -> conHasUnresolved row
    TDisjoint left right body -> anyMElab conHasUnresolved [left, right, body]
    CApp function argument -> anyMElab conHasUnresolved [function, argument]
    CAbs _ _ body -> conHasUnresolved body
    CKAbs _ body -> conHasUnresolved body
    CKApp function _ -> conHasUnresolved function
    TKFun _ body -> conHasUnresolved body
    CRecord _ fields -> anyMElab conHasUnresolved (concatMap (\(name, value) -> [name, value]) fields)
    CConcat left right -> anyMElab conHasUnresolved [left, right]
    CTuple elements -> anyMElab conHasUnresolved elements
    CProj tuple _ -> conHasUnresolved tuple
    _ -> pure False

anyMElab :: (value -> ElabM Bool) -> [value] -> ElabM Bool
anyMElab _ [] = pure False
anyMElab predicate (value : rest) = do
  found <- predicate value
  if found then pure True else anyMElab predicate rest

type MetaRoots = ([Kind], [Con])

declarationRoots :: Decl -> MetaRoots
declarationRoots declaration = case locatedValue declaration of
  DCon _ _ kind constructor -> ([kind], [constructor])
  DDatatype definitions -> datatypeRoots definitions
  DDatatypeImp _ _ _ _ _ _ constructors -> constructorPayloadRoots constructors
  DVal _ _ typ expression -> (expressionKinds expression, typ : expressionConstructors expression)
  DValRec bindings ->
    ( concatMap (\(_, _, _, expression) -> expressionKinds expression) bindings
    , concatMap (\(_, _, typ, expression) -> typ : expressionConstructors expression) bindings
    )
  DSgn _ _ signature -> signatureRoots signature
  DStr _ _ signature structure -> signatureRoots signature <> structureRoots structure
  DFfiStr _ _ signature -> signatureRoots signature
  DConstraint left right -> ([], [left, right])
  DExport _ signature structure -> signatureRoots signature <> structureRoots structure
  DTable _ _ _ row primary keys constraints uniques ->
    ( expressionKinds primary <> expressionKinds constraints
    , [row, keys, uniques] <> expressionConstructors primary <> expressionConstructors constraints
    )
  DSequence {} -> mempty
  DView _ _ _ expression typ -> (expressionKinds expression, typ : expressionConstructors expression)
  DIndex first second -> (expressionKinds first <> expressionKinds second, expressionConstructors first <> expressionConstructors second)
  DDatabase {} -> mempty
  DCookie _ _ _ typ -> ([], [typ])
  DStyle {} -> mempty
  DTask kind expression -> (expressionKinds kind <> expressionKinds expression, expressionConstructors kind <> expressionConstructors expression)
  DPolicy expression -> (expressionKinds expression, expressionConstructors expression)
  DOnError {} -> mempty
  DFfi _ _ _ typ -> ([], [typ])

datatypeRoots :: [(String, GlobalId, [String], [(String, GlobalId, Maybe Con)])] -> MetaRoots
datatypeRoots = foldMap (constructorPayloadRoots . fourth)
  where
    fourth (_, _, _, constructors) = constructors

constructorPayloadRoots :: [(String, GlobalId, Maybe Con)] -> MetaRoots
constructorPayloadRoots constructors = ([], [payload | (_, _, Just payload) <- constructors])

signatureRoots :: Signature -> MetaRoots
signatureRoots signature = case locatedValue signature of
  SgnConst items -> foldMap signatureItemRoots items
  SgnFun _ _ domain range -> signatureRoots domain <> signatureRoots range
  SgnWhere base _ _ definition -> signatureRoots base <> ([], [definition])
  _ -> mempty

signatureItemRoots :: SigItem -> MetaRoots
signatureItemRoots item = case locatedValue item of
  SgiConAbs _ _ kind -> ([kind], [])
  SgiCon _ _ kind definition -> ([kind], [definition])
  SgiDatatype definitions -> datatypeRoots definitions
  SgiDatatypeImp _ _ _ _ _ _ constructors -> constructorPayloadRoots constructors
  SgiVal _ _ typ -> ([], [typ])
  SgiStr _ _ _ signature -> signatureRoots signature
  SgiSgn _ _ signature -> signatureRoots signature
  SgiConstraint left right -> ([], [left, right])
  SgiClassAbs _ _ kind -> ([kind], [])
  SgiClass _ _ kind definition -> ([kind], [definition])

structureRoots :: Structure -> MetaRoots
structureRoots structure = case locatedValue structure of
  -- nestedDeclarationsFirst already visits every declaration here before its
  -- enclosing structure. The enclosing pass still checks its own signature
  -- and functor parameter/result signatures below.
  StrConst _ -> mempty
  StrProj base _ -> structureRoots base
  StrFun _ _ domain range body -> signatureRoots domain <> signatureRoots range <> structureRoots body
  StrApp function argument -> structureRoots function <> structureRoots argument
  _ -> mempty

expressionConstructors :: Expr -> [Con]
expressionConstructors expression = case locatedValue expression of
  EApp function argument -> descend [function, argument]
  EAbs _ domain range body -> [domain, range] <> expressionConstructors body
  ECApp function argument -> argument : expressionConstructors function
  ECAbs _ _ _ body -> expressionConstructors body
  EKAbs _ body -> expressionConstructors body
  EKApp function _ -> expressionConstructors function
  ERecord fields -> concatMap (\(name, value, typ) -> [name, typ] <> expressionConstructors value) fields
  EField record name fieldType rest -> [name, fieldType, rest] <> expressionConstructors record
  EConcat left leftRow right rightRow -> [leftRow, rightRow] <> descend [left, right]
  ECut record field fieldType rest -> [field, fieldType, rest] <> expressionConstructors record
  ECutMulti record fields rest -> [fields, rest] <> expressionConstructors record
  ECase scrutinee branches input result -> [input, result] <> expressionConstructors scrutinee <> concatMap branchConstructors branches
  ELet declarations body typ -> typ : concatMap eDeclarationConstructors declarations <> expressionConstructors body
  _ -> []
  where
    descend = concatMap expressionConstructors
    branchConstructors (pattern', branch) = patternConstructors pattern' <> expressionConstructors branch

expressionKinds :: Expr -> [Kind]
expressionKinds expression = case locatedValue expression of
  EApp function argument -> descend [function, argument]
  EAbs _ _ _ body -> expressionKinds body
  ECApp function _ -> expressionKinds function
  ECAbs _ _ kind body -> kind : expressionKinds body
  EKAbs _ body -> expressionKinds body
  EKApp function kind -> kind : expressionKinds function
  ERecord fields -> concatMap (expressionKinds . middle) fields
  EField record _ _ _ -> expressionKinds record
  EConcat left _ right _ -> descend [left, right]
  ECut record _ _ _ -> expressionKinds record
  ECutMulti record _ _ -> expressionKinds record
  ECase scrutinee branches _ _ -> expressionKinds scrutinee <> concatMap (expressionKinds . snd) branches
  ELet declarations body _ -> concatMap eDeclarationKinds declarations <> expressionKinds body
  _ -> []
  where
    descend = concatMap expressionKinds
    middle (_, value, _) = value

patternConstructors :: Pattern -> [Con]
patternConstructors pattern' = case locatedValue pattern' of
  PVar _ typ -> [typ]
  PCon _ _ arguments payload -> arguments <> maybe [] patternConstructors payload
  PRecord fields _ -> concatMap (\(_, nested, typ) -> typ : patternConstructors nested) fields
  _ -> []

eDeclarationConstructors :: EDecl -> [Con]
eDeclarationConstructors declaration = case locatedValue declaration of
  EDVal pattern' typ expression -> typ : patternConstructors pattern' <> expressionConstructors expression
  EDValRec bindings -> concatMap (\(_, typ, expression) -> typ : expressionConstructors expression) bindings

eDeclarationKinds :: EDecl -> [Kind]
eDeclarationKinds declaration = case locatedValue declaration of
  EDVal _ _ expression -> expressionKinds expression
  EDValRec bindings -> concatMap (expressionKinds . third) bindings
  where
    third (_, _, expression) = expression
