-- | Lower specialized, module-free Core into the backend-neutral monomorphic
-- IR.  Intrinsics keep resolved static operands, allowing later direct JS and
-- LLVM backends to choose their own runtime strategy without reconstructing
-- Ur's type-level computation.
module Vr.Mono.Lower
  ( monoizeFile
  , monoizeFileWithSettings
  , monoizeFileWithSemanticSettings
  , monoizeFileWithProjectSettings
  ) where

import Control.Monad (foldM, guard, when, zipWithM)
import Control.Monad.State.Strict (StateT (..))
import qualified Data.ByteString.Char8 as ByteString
import Data.Char (toLower, toUpper)
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import qualified Vr.Core.Optimize as Optimize
import qualified Vr.Core.Reduce as Reduce
import qualified Vr.Core.Semantics as Semantics
import qualified Vr.Core.Substitute as Substitute
import qualified Vr.Core.Syntax as C
import qualified Vr.Mono.Lower.State as State
import qualified Vr.Mono.Syntax as M
import qualified Vr.Mono.Validate as Validate
import Vr.Middle (DbMode (DbModePending), Sidedness (PlacementPending))
import Vr.Source (Diagnostic, DiagnosticPhase (MonoPhase), Located (..), Primitive (..), Span, StringMode (HtmlString, NormalString), diagnostic)

monoizeFile :: C.File -> Either [Diagnostic] M.File
monoizeFile = monoizeFileWithSettings Reduce.defaultReduceSettings

monoizeFileWithSettings :: Reduce.ReduceSettings -> C.File -> Either [Diagnostic] M.File
monoizeFileWithSettings settings =
  monoizeFileWithSemanticSettings settings Semantics.defaultSemanticSettings

monoizeFileWithSemanticSettings
  :: Reduce.ReduceSettings
  -> Semantics.SemanticSettings
  -> C.File
  -> Either [Diagnostic] M.File
monoizeFileWithSemanticSettings settings semanticSettings core = do
  monoizeFileWithProjectSettings settings semanticSettings "/" "postgres" True core

monoizeFileWithProjectSettings
  :: Reduce.ReduceSettings
  -> Semantics.SemanticSettings
  -> String
  -> String
  -> Bool
  -> C.File
  -> Either [Diagnostic] M.File
monoizeFileWithProjectSettings settings semanticSettings urlPrefix databaseSystem mangleSqlNames core = do
  specialized <- Optimize.optimizeFileWithSettings settings semanticSettings core
  let initial = (State.initialMonoState (maximumGlobal specialized + 1) specialized)
        { State.monoUrlPrefix = urlPrefix
        , State.monoClientToServer = Semantics.semanticClientToServer semanticSettings
        }
      valueInfo = collectValueInfo specialized
      tableName = physicalTableName databaseSystem mangleSqlNames
      relationName = physicalRelationName databaseSystem mangleSqlNames
      schemaNames = Map.map tableName (collectSchemaNames specialized)
  case State.runMonoM initial
      (fmap concat (mapM (monoDeclaration valueInfo schemaNames tableName relationName) specialized)) of
    Left problem -> Left [problem]
    Right (declarations, final) ->
      let generated = reverse (State.monoGeneratedDatatypes final)
            <> reverse (State.monoGeneratedValues final)
          modes = [(identifier, PlacementPending, DbModePending) | identifier <- runtimeValueIds (generated <> declarations)]
          file = M.File
            { M.fileDeclarations = generated <> declarations
            , M.fileFunctionModes = modes
            }
       in case Validate.validateFile file of
            Left problems -> Left problems
            Right valid -> Right valid

type ValueInfo = Map.Map C.GlobalId (C.Con, String)

-- Ur/Web applies physical SQL mangling only when Core becomes Mono.  Keeping
-- logical paths in Core is important for rewrite matching, while every value
-- that reaches a backend must already contain the database-visible relation
-- name.  MySQL folds the whole identifier; PostgreSQL and SQLite retain the
-- module/path casing and only adjust the first character when mangling is
-- disabled.
physicalTableName :: String -> Bool -> String -> String
physicalTableName databaseSystem mangle name
  | map toLower databaseSystem == "mysql" = prefix <> map toLower name
  | mangle = "uw_" <> capitalizeFirst name
  | otherwise = lowercaseFirst name
  where
    prefix = if mangle then "uw_" else ""

physicalRelationName :: String -> Bool -> String -> String
physicalRelationName databaseSystem mangle name
  | map toLower databaseSystem == "mysql" = prefix <> map toLower name
  | mangle = "uw_" <> name
  | otherwise = lowercaseFirst name
  where
    prefix = if mangle then "uw_" else ""

lowercaseFirst :: String -> String
lowercaseFirst [] = []
lowercaseFirst (first : rest) = toLower first : rest

capitalizeFirst :: String -> String
capitalizeFirst [] = []
capitalizeFirst (first : rest) = toUpper first : rest

monoDeclaration
  :: ValueInfo
  -> Map.Map C.GlobalId String
  -> (String -> String)
  -> (String -> String)
  -> C.Decl
  -> State.MonoM [M.Decl]
monoDeclaration values schemaNames tableName relationName declaration = case locatedValue declaration of
  C.DCon {} -> pure []
  C.DForeign moduleName name typ -> case foreignRuntimeSignature typ of
    -- Core keeps foreign signatures as metadata for Vr's native backend,
    -- whereas Ur/Web keeps them in its compiler environment.  A polymorphic
    -- foreign value has no single native ABI signature: its constructor and
    -- kind binders are erased at client-side call sites, and jsFunc supplies
    -- the JavaScript arity independently.  Do not invent a concrete ABI here.
    -- If such a value is used on the server, LLVM reports the missing concrete
    -- signature at that use instead of silently compiling it with the wrong
    -- int/float/pointer calling convention.
    Nothing -> pure []
    Just runtimeType -> do
      typ' <- State.monoType runtimeType
      pure [at (M.DForeign moduleName name typ')]
  C.DDatatype definitions -> do
    definitions' <- mapM monoDatatypeDefinition definitions
    pure [at (M.DDatatype definitions')]
  C.DVal name identifier typ expression url -> do
    typ' <- State.monoType typ
    expression' <- monoExpr expression
    pure [at (M.DVal name identifier typ' expression' url)]
  C.DValRec bindings -> do
    bindings' <- mapM monoBinding bindings
    pure [at (M.DValRec bindings')]
  C.DExport kind identifier protected -> case Map.lookup identifier values of
    Nothing -> monoFailure declaration "export-value" "Export target has no value declaration"
    Just (typ, url) -> do
      let (arguments, result) = unwindExport typ
      arguments' <- mapM State.monoType arguments
      result' <- State.monoType result
      pure [at (M.DExport kind url identifier arguments' result' protected)]
  C.DTable name identifier row sqlName primary _ constraints _ -> do
    fields <- monoRow row
    primary' <- monoExpr primary
    constraints' <- monoExpr constraints
    pure
      [ at (M.DTable (tableName sqlName) fields primary' constraints')
      , runtimeNameValue location name identifier (tableName sqlName) NormalString
      ]
  C.DSequence name identifier sqlName ->
    pure
      [ at (M.DSequence (relationName sqlName))
      , runtimeNameValue location name identifier (relationName sqlName) NormalString
      ]
  C.DView name identifier sqlName expression row -> do
    fields <- monoRow row
    expression' <- monoExpr expression
    pure
      [ at (M.DView (tableName sqlName) fields expression')
      , runtimeNameValue location name identifier (tableName sqlName) NormalString
      ]
  C.DIndex table modes -> do
    case staticIndex schemaNames table modes of
      Just (physicalTable, fields) -> pure [at (M.DIndex physicalTable fields)]
      -- The reference compiler accepts an index only after Core reduction has
      -- exposed a named table and a literal record of indexing modes.  It
      -- reports "Unsupported declaration" from Monoize for every other
      -- shape; there is no run-time or backend form of a dynamic index.
      Nothing -> monoFailure declaration "index-declaration"
        "Unsupported database index declaration after monomorphization"
  C.DDatabase connection -> pure [at (M.DDatabaseRaw connection)]
  C.DCookie name identifier _ runtimeName -> do
    let physicalName = if null runtimeName then name else runtimeName
    pure
      [ at (M.DCookie physicalName)
      , runtimeNameValue location name identifier physicalName NormalString
      ]
  C.DStyle name identifier runtimeName ->
    pure
      [ at (M.DStyle runtimeName)
      , runtimeNameValue location name identifier runtimeName HtmlString
      ]
  C.DTask kind body -> do
    kind' <- monoExpr kind
    body' <- monoExpr body
    pure [at (M.DTask kind' body')]
  C.DPolicy expression -> monoPolicies expression
  C.DOnError identifier -> pure [at (M.DOnError identifier)]
  where
    location = locatedSpan declaration
    at = Located (locatedSpan declaration)
    monoBinding (name, identifier, typ, expression, url) =
      (,,,,) name identifier <$> State.monoType typ <*> monoExpr expression <*> pure url

    monoDatatypeDefinition (name, identifier, parameters, constructors)
      | null parameters =
          (,,) name identifier <$> mapM monoDatatypeConstructor constructors
      | otherwise =
          monoFailure declaration "polymorphic-datatype-late"
            ("Polymorphic datatype " <> name <> " survived Core Specialize")

    monoDatatypeConstructor (name, identifier, payload) =
      (,,) name identifier <$> traverse State.monoType payload

    -- Ur/Web splits a source policy joined with Basis.also into independent
    -- Mono declarations, then removes the policy constructor itself.  Keep
    -- that structure in Vr's target-neutral IR so the information-flow pass
    -- and every backend see the policy kind explicitly instead of having to
    -- reverse-engineer a general expression after monomorphisation.
    monoPolicies expression = case locatedValue expression of
      C.EFfiApp "Basis" "also" [(left, _), (right, _)] ->
        (<>) <$> monoPolicies left <*> monoPolicies right
      _ -> do
        let (makePolicy, payload) = classifyPolicy expression
        payload' <- monoExpr payload
        pure [at (M.DPolicy (makePolicy payload'))]

    classifyPolicy expression = case locatedValue expression of
      C.EApp function payload
        | basisExpressionName function == Just "sendClient" -> (M.PolicyClient, payload)
        | basisExpressionName function == Just "mayInsert" -> (M.PolicyInsert, payload)
        | basisExpressionName function == Just "mayDelete" -> (M.PolicyDelete, payload)
        | basisExpressionName function == Just "mayUpdate" -> (M.PolicyUpdate, payload)
      C.EFfiApp "Basis" "sendOwnIds" [(payload, _)] -> (M.PolicySequence, payload)
      -- The elaborator has already checked sql_policy, and the reference
      -- compiler diagnoses an unexpected constructor during Mono.  Retain it
      -- as a client policy here so a later information-flow diagnostic keeps
      -- the original source span instead of silently discarding the policy.
      _ -> (M.PolicyClient, expression)

foreignRuntimeSignature :: C.Con -> Maybe C.Con
foreignRuntimeSignature typ =
  let normalized = Substitute.normalizeCon typ
   in case locatedValue normalized of
        C.TCFun {} -> Nothing
        C.TKFun {} -> Nothing
        _ -> Just normalized

runtimeNameValue :: Span -> String -> M.GlobalId -> String -> StringMode -> M.Decl
runtimeNameValue location name identifier physicalName mode =
  Located location
    (M.DVal
      name
      identifier
      (Located location (M.TFfi "Basis" "string"))
      (Located location (M.EPrim (PrimString mode (ByteString.pack physicalName))))
      physicalName)

staticIndex :: Map.Map C.GlobalId String -> C.Expr -> C.Expr -> Maybe (String, [(String, M.IndexMode)])
staticIndex schemaNames table modes = do
  identifier <- case locatedValue table of
    C.ENamed found -> Just found
    _ -> Nothing
  tableName <- Map.lookup identifier schemaNames
  guard (not (null tableName))
  fields <- case locatedValue modes of
    C.ERecord entries -> mapM field entries
    _ -> Nothing
  pure (tableName, sortOn fst fields)
  where
    field (name, mode, _) = do
      fieldName <- case locatedValue name of
        C.CName found -> Just found
        _ -> Nothing
      indexMode <- case basisExpressionName mode of
        Just "equality" -> Just M.IndexEquality
        Just "trigram" -> Just M.IndexTrigram
        Just "skipped" -> Just M.IndexSkipped
        _ -> Nothing
      pure (fieldName, indexMode)

basisExpressionName :: C.Expr -> Maybe String
basisExpressionName expression = case locatedValue expression of
  C.EFfi "Basis" name -> Just name
  C.EApp function _ -> basisExpressionName function
  C.ECApp function _ -> basisExpressionName function
  _ -> Nothing

monoExpr :: C.Expr -> State.MonoM M.Expr
monoExpr source = case locatedValue source of
  C.EPrim primitive -> pure (at (M.EPrim primitive))
  C.ERel index -> pure (at (M.ERel index))
  C.ENamed identifier -> pure (at (M.ENamed identifier))
  C.ECon C.Option constructor arguments payload -> monoOption source constructor arguments payload
  C.ECon classification constructor arguments payload -> do
    constructor' <- State.monoPatCon constructor arguments
    payload' <- traverse monoExpr payload
    pure (at (M.ECon classification constructor' payload'))
  C.EFfi moduleName name -> lowerFfiValue source moduleName name
  C.EFfiApp moduleName name arguments -> case (moduleName, name, arguments) of
    ("Basis", "classes", [(left, _), (right, _)]) ->
      lowerSeparatedStrings source " " left right
    ("Basis", "data_attr", [(kind, _), (key, _), (value, _)]) ->
      lowerDataAttribute source kind key value
    ("Basis", "data_attrs", [(left, _), (right, _)]) ->
      lowerSeparatedStrings source " " left right
    ("Basis", "atom", [(value, _)]) -> lowerCssAtom source value
    ("Basis", "css_url", [(value, _)]) -> lowerCssUrl source value
    ("Basis", "property", [(value, _)]) -> lowerCssProperty source value
    ("Basis", "value", [(property, _), (value, _)]) ->
      lowerSeparatedStrings source " " property value
    ("Basis", "oneProperty", [(style, _), (property, _)]) ->
      lowerStyleProperty source style property
    _ -> do
      arguments' <- mapM typedExpr arguments
      case (moduleName, name, arguments') of
        ("Basis", "sleep", [(value, _)]) -> pure (at (M.ESleep value))
        ("Basis", "spawn", [(value, _)]) -> pure (at (M.ESpawn value))
        _ -> pure (at (M.EFfiApp moduleName name [] arguments'))
  C.EApp function argument -> case coreStringApplication source of
    Just lowered -> lowered
    Nothing -> case textBlobReturn function argument of
      Just (resultType, content) -> lowerTextBlobReturn source resultType content
      Nothing -> case coreBasisApplication function of
        Just ("sleep", []) -> at . M.ESleep <$> monoExpr argument
        Just ("spawn", []) -> at . M.ESpawn <$> monoExpr argument
        Just ("recv", [resultType]) ->
          at <$> (M.ERecv <$> monoExpr argument <*> State.monoType resultType)
        _ -> at <$> (M.EApp <$> monoExpr function <*> monoExpr argument)
  C.EAbs name domain range body ->
    at <$> (M.EAbs name <$> State.monoType domain <*> State.monoType range <*> monoExpr body)
  C.ECApp function argument
    | Just ("transaction_bind", [firstType, resultType]) <- coreBasisApplication source ->
        lowerTransactionBind source firstType resultType
    | Just ("signal_bind", [firstType, resultType]) <- coreBasisApplication source ->
        lowerSignalBind source firstType resultType
    | otherwise -> lowerStaticApplication source function argument
  C.ECAbs {} -> monoFailure source "polymorphic-expression" "Constructor abstraction survived Core specialization"
  C.EKAbs {} -> monoFailure source "polymorphic-expression" "Kind abstraction survived Core specialization"
  C.EKApp {} -> monoFailure source "polymorphic-expression" "Kind application survived Core specialization"
  C.ERecord fields -> at . M.ERecord . sortOn monoRecordFieldName <$> mapM recordField fields
  C.EField record field _ _ -> at <$> (M.EField <$> monoExpr record <*> State.monoStaticArg field)
  C.EConcat left _ right _ -> at <$> (M.ERecordConcat <$> monoExpr left <*> monoExpr right)
  C.ECut record field _ _ -> do
    record' <- monoExpr record
    field' <- State.monoStaticArg field
    pure (at (M.ERecordCut record' [field']))
  C.ECutMulti record fields _ -> do
    record' <- monoExpr record
    names <- rowNames fields
    pure (at (M.ERecordCut record' names))
  C.ECase scrutinee branches input result ->
    at <$> (M.ECase <$> monoExpr scrutinee <*> mapM branch branches <*> State.monoType input <*> State.monoType result)
  C.EWrite expression -> do
    expression' <- monoExpr (Substitute.liftExprValues 0 1 expression)
    let unit = State.unitType (locatedSpan source)
    pure (at (M.EAbs "_" unit unit (at (M.EWrite expression'))))
  C.EClosure identifier values -> at . M.EClosure identifier <$> mapM monoExpr values
  C.ELet name typ value body ->
    at <$> (M.ELet name <$> State.monoType typ <*> monoExpr value <*> monoExpr body)
  C.EServerCall identifier arguments typ failureMode -> do
    target <- State.lookupRpcTarget identifier
    (functionType, url, effect) <- case target of
      Just found -> pure found
      Nothing -> monoFailure source "rpc-target" "RPC call has no exported target metadata"
    arguments' <- mapM monoExpr arguments
    domains <- State.monoFunctionDomains (length arguments) functionType
    encoded <- zipWithM (urlifyMono source) arguments' domains
    typ' <- State.monoType typ
    prefix <- State.getUrlPrefix
    let text value = at (M.EPrim (PrimString NormalString (ByteString.pack value)))
        route = text (mountRpcPath prefix url)
        append current argument = at (M.EStrcat current (at (M.EStrcat (text "/") argument)))
        call = foldl append route encoded
    pure (at (M.EServerCall call typ' effect failureMode))
  where
    at = Located (locatedSpan source)
    typedExpr (expression, typ) = (,) <$> monoExpr expression <*> State.monoType typ
    recordField (field, value, typ) = (,,) <$> State.monoStaticArg field <*> monoExpr value <*> State.monoType typ
    branch (pattern', body) = (,) <$> monoPattern pattern' <*> monoExpr body

mountRpcPath :: String -> String -> String
mountRpcPath prefix url = case (prefix, dropWhile (== '/') url) of
  ("", path) -> '/' : path
  ("/", path) -> '/' : path
  (mounted, path) -> reverse (dropWhile (== '/') (reverse mounted)) <> "/" <> path

lowerStaticApplication :: C.Expr -> C.Expr -> C.Con -> State.MonoM M.Expr
lowerStaticApplication source function argument = case locatedValue function of
  C.EFfi "Basis" "error" -> lowerError source argument
  C.EFfi "Basis" "serialize" -> lowerSerialize source argument
  C.EFfi "Basis" "deserialize" -> lowerDeserialize source argument
  C.EFfi "Basis" "unsafeSerializedToString" -> lowerSerializedIdentity source
  C.EFfi "Basis" "unsafeSerializedFromString" -> lowerSerializedIdentity source
  C.EFfi "Basis" "show" -> lowerShowIdentity source argument
  C.EFfi "Basis" "mkShow" -> lowerShowIdentity source argument
  C.EFfi "Basis" "eq" -> lowerEqSelector source argument False
  C.EFfi "Basis" "ne" -> lowerEqSelector source argument True
  C.EFfi "Basis" "mkEq" -> lowerEqSelector source argument False
  C.EFfi "Basis" name
    | Just field <- lookup name [("lt", "Lt"), ("le", "Le")] ->
        lowerOrderSelector source argument field False
  C.EFfi "Basis" name
    | Just field <- lookup name [("gt", "Le"), ("ge", "Lt")] ->
        lowerOrderSelector source argument field True
  C.EFfi "Basis" "mkOrd" -> lowerOrderIdentity source argument
  C.EFfi "Basis" "read" -> lowerReadSelector source argument "Read"
  C.EFfi "Basis" "readError" -> lowerReadSelector source argument "ReadError"
  C.EFfi "Basis" "mkRead" -> lowerMkRead source argument
  C.EFfi "Basis" name
    | Just field <- lookup name
        [ ("zero", "Zero")
        , ("neg", "Neg")
        , ("plus", "Plus")
        , ("minus", "Minus")
        , ("times", "Times")
        , ("divide", "Div")
        , ("mod", "Mod")
        , ("pow", "Pow")
        ] -> lowerNumericSelector source argument field
  C.EFfi "Basis" "getCookie" -> lowerGetCookie source argument
  C.EFfi "Basis" "setCookie" -> lowerSetCookie source argument
  C.EFfi "Basis" "clearCookie" -> lowerClearCookie source
  C.EFfi "Basis" "redirect" -> lowerRedirect source argument
  C.EFfi "Basis" "returnBlob" -> lowerReturnBlob source argument
  C.EFfi "Basis" "transaction_return" -> lowerTransactionReturn source argument
  C.EFfi "Basis" "source" -> lowerSource source argument
  C.EFfi "Basis" "set" -> lowerSetSource source argument
  C.EFfi "Basis" "get" -> lowerGetSource source argument
  C.EFfi "Basis" "current" -> lowerCurrentSignal source argument
  C.EFfi "Basis" "signal_return" -> lowerSignalReturn source argument
  C.EFfi "Basis" "signal" -> lowerSignalSource source argument
  _ -> do
    function' <- monoExpr function
    static <- State.monoStaticArg argument
    case locatedValue function' of
      M.EFfi {} -> pure (resolveStaticFfi source (appendStatic source function' static))
      M.EFfiApp {} -> pure (resolveStaticFfi source (appendStatic source function' static))
      _ | ffiHead function' -> pure (appendStatic source function' static)
      _ -> monoFailure source "polymorphic-expression" "Constructor application of a non-FFI value survived Core specialization"

lowerFfiValue :: C.Expr -> String -> String -> State.MonoM M.Expr
lowerFfiValue source moduleName name
  | moduleName == "Basis", name `elem` ["null", "noStyle"] =
      pure (stringExpression source "")
  | moduleName == "Basis", name == "data_kind" =
      pure (stringExpression source "data-")
  | moduleName == "Basis", name == "aria_kind" =
      pure (stringExpression source "aria-")
  | moduleName == "Basis"
  , Just (typeName, operator, intness) <- lookup name
      [ ("eq_int", ("int", "==", M.IntegerBinop))
      , ("eq_float", ("float", "==", M.GeneralBinop))
      , ("eq_string", ("string", "!strcmp", M.GeneralBinop))
      , ("eq_char", ("char", "==", M.GeneralBinop))
      , ("eq_bool", ("bool", "==", M.GeneralBinop))
      ] = pure (comparisonFunctionValue source typeName intness operator)
  | moduleName == "Basis"
  , name == "eq_time" = pure (timeComparisonFunctionValue source "eq_time")
  | moduleName == "Basis"
  , Just (typeName, intness) <- lookup name
      [ ("ord_int", ("int", M.IntegerBinop))
      , ("ord_float", ("float", M.GeneralBinop))
      , ("ord_bool", ("bool", M.GeneralBinop))
      , ("ord_char", ("char", M.GeneralBinop))
      ] = pure (orderDictionaryValue source typeName intness)
  | moduleName == "Basis"
  , name == "ord_string" = pure (stringOrderDictionaryValue source)
  | moduleName == "Basis"
  , name == "ord_time" = pure (timeOrderDictionaryValue source)
  | moduleName == "Basis"
  , Just typeName <- lookup name
      [ ("read_int", "int")
      , ("read_float", "float")
      , ("read_char", "char")
      , ("read_bool", "bool")
      , ("read_time", "time")
      ] = pure (readDictionaryValue source typeName)
  | moduleName == "Basis"
  , name == "read_string" = pure (stringReadDictionaryValue source)
  | moduleName == "Basis"
  , name == "num_int" = pure (numericDictionaryValue source "int" M.IntegerBinop (PrimInt 0)
      [("Plus", "+"), ("Minus", "-"), ("Times", "*"), ("Div", "/"), ("Mod", "%"), ("Pow", "powl")])
  | moduleName == "Basis"
  , name == "num_float" = pure (numericDictionaryValue source "float" M.GeneralBinop (PrimFloat 0)
      [("Plus", "+"), ("Minus", "-"), ("Times", "*"), ("Div", "fdiv"), ("Mod", "fmod"), ("Pow", "powf")])
  | moduleName == "Basis"
  , Just typ <- lookup name
      [ ("show_int", "int")
      , ("show_float", "float")
      , ("show_char", "char")
      , ("show_bool", "bool")
      , ("show_time", "time")
      ] = do
      let location = locatedSpan source
          at = Located location
          domain = at (M.TFfi "Basis" typ)
          string = at (M.TFfi "Basis" "string")
          runtimeName = case typ of
            "int" -> "intToString"
            "float" -> "floatToString"
            "char" -> "charToString"
            "bool" -> "boolToString"
            _ -> "timeToString"
          body = at (M.EFfiApp "Basis" runtimeName [] [(at (M.ERel 0), domain)])
      pure (at (M.EAbs "value" domain string body))
  | moduleName == "Basis"
  , name `elem` ["show_string", "show_queryString", "show_url", "show_css_class", "show_id"] = do
      let location = locatedSpan source
          at = Located location
          string = at (M.TFfi "Basis" "string")
      pure (at (M.EAbs "value" string string (at (M.ERel 0))))
  | otherwise = pure (Located (locatedSpan source) (M.EFfi moduleName name []))

-- These rewrites intentionally mirror Monoize's string representation for
-- classes, styles, and data/ARIA attributes.  Backends therefore consume one
-- common, already-sanitized representation instead of inventing target-local
-- CSS or attribute semantics.
lowerSeparatedStrings :: C.Expr -> String -> C.Expr -> C.Expr -> State.MonoM M.Expr
lowerSeparatedStrings source separator left right = do
  left' <- monoExpr left
  right' <- monoExpr right
  pure (Located (locatedSpan source)
    (M.EStrcat left' (Located (locatedSpan source)
      (M.EStrcat (stringExpression source separator) right'))))

lowerDataAttribute :: C.Expr -> C.Expr -> C.Expr -> C.Expr -> State.MonoM M.Expr
lowerDataAttribute source kind key value = do
  kind' <- monoExpr kind
  key' <- monoExpr key
  value' <- monoExpr value
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
      checkedKey = at (M.EFfiApp "Basis" "blessData" [] [(key', string)])
      escapedValue = at (M.EFfiApp "Basis" "attrifyString" [] [(value', string)])
  pure (at (M.EStrcat kind'
    (at (M.EStrcat checkedKey
      (at (M.EStrcat (stringExpression source "=\"")
        (at (M.EStrcat escapedValue (stringExpression source "\"")))))))))

lowerCssAtom :: C.Expr -> C.Expr -> State.MonoM M.Expr
lowerCssAtom source value = do
  value' <- monoExpr value
  case monoStringLiteral value' of
    Just literal
      | validCssAtom literal -> pure value'
      | otherwise -> monoFailure source "css-atom" ("Invalid string " <> ByteString.unpack literal <> " passed to 'atom'")
    Nothing -> do
      let at = Located (locatedSpan source)
          string = at (M.TFfi "Basis" "string")
      pure (at (M.EFfiApp "Basis" "atom" [] [(value', string)]))

lowerCssUrl :: C.Expr -> C.Expr -> State.MonoM M.Expr
lowerCssUrl source value = do
  value' <- monoExpr value
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
      checked = at (M.EFfiApp "Basis" "css_url" [] [(value', string)])
  pure (at (M.EStrcat (stringExpression source "url(")
    (at (M.EStrcat checked (stringExpression source ")")))))

lowerCssProperty :: C.Expr -> C.Expr -> State.MonoM M.Expr
lowerCssProperty source value = do
  value' <- monoExpr value
  checked <- case monoStringLiteral value' of
    Just literal
      | validCssProperty literal -> pure value'
      | otherwise -> monoFailure source "css-property" ("Invalid string " <> ByteString.unpack literal <> " passed to 'property'")
    Nothing -> do
      let at = Located (locatedSpan source)
          string = at (M.TFfi "Basis" "string")
      pure (at (M.EFfiApp "Basis" "property" [] [(value', string)]))
  let at = Located (locatedSpan source)
  pure (at (M.EStrcat checked (stringExpression source ":")))

lowerStyleProperty :: C.Expr -> C.Expr -> C.Expr -> State.MonoM M.Expr
lowerStyleProperty source style property = do
  style' <- monoExpr style
  property' <- monoExpr property
  let at = Located (locatedSpan source)
  pure (at (M.EStrcat style'
    (at (M.EStrcat property' (stringExpression source ";")))))

stringExpression :: C.Expr -> String -> M.Expr
stringExpression source value = Located (locatedSpan source)
  (M.EPrim (PrimString NormalString (ByteString.pack value)))

monoStringLiteral :: M.Expr -> Maybe ByteString.ByteString
monoStringLiteral expression = case locatedValue expression of
  M.EPrim (PrimString _ value) -> Just value
  _ -> Nothing

validCssAtom :: ByteString.ByteString -> Bool
validCssAtom = ByteString.all (\character ->
  asciiAlphaNumeric character || character `elem` ['+', '-', '.', '%', '#'])

validCssProperty :: ByteString.ByteString -> Bool
validCssProperty bytes = case ByteString.unpack bytes of
  first : rest ->
    (cssNameStart first || case rest of
      second : _ -> first == '-' && cssNameStart second
      [] -> False)
      && all cssNameCharacter rest
  [] -> False
  where
    cssNameStart character = asciiAlpha character || character == '_'
    cssNameCharacter character = cssNameStart character || asciiDigit character || character == '-'

asciiAlphaNumeric :: Char -> Bool
asciiAlphaNumeric character = asciiAlpha character || asciiDigit character

asciiAlpha :: Char -> Bool
asciiAlpha character =
  ('A' <= character && character <= 'Z') || ('a' <= character && character <= 'z')

asciiDigit :: Char -> Bool
asciiDigit character = '0' <= character && character <= '9'

coreStringApplication :: C.Expr -> Maybe (State.MonoM M.Expr)
coreStringApplication source = case collect source [] of
  (function, [left, right]) | basisName function == Just "join" ->
    Just (Located (locatedSpan source) <$> (M.EStrcat <$> monoExpr left <*> monoExpr right))
  -- Basis.useMore only weakens the phantom set of form fields required by an
  -- XML fragment.  Ur/Web's Monoize pass erases it to its value argument.
  (function, [value]) | basisName function == Just "useMore" ->
    Just (monoExpr value)
  (function, [value]) | basisName function == Just "cdata" -> Just $ do
    value' <- monoExpr value
    let at = Located (locatedSpan source)
        string = at (M.TFfi "Basis" "string")
    pure (at (M.EFfiApp "Basis" "htmlifyString" [] [(value', string)]))
  (function, [left, right]) | basisName function == Just "classes" ->
    Just (lowerSeparatedStrings source " " left right)
  (function, [kind, key, value]) | basisName function == Just "data_attr" ->
    Just (lowerDataAttribute source kind key value)
  (function, [left, right]) | basisName function == Just "data_attrs" ->
    Just (lowerSeparatedStrings source " " left right)
  (function, [value]) | basisName function == Just "atom" ->
    Just (lowerCssAtom source value)
  (function, [value]) | basisName function == Just "css_url" ->
    Just (lowerCssUrl source value)
  (function, [value]) | basisName function == Just "property" ->
    Just (lowerCssProperty source value)
  (function, [property, value]) | basisName function == Just "value" ->
    Just (lowerSeparatedStrings source " " property value)
  (function, [style, property]) | basisName function == Just "oneProperty" ->
    Just (lowerStyleProperty source style property)
  _ -> Nothing
  where
    collect expression arguments = case locatedValue expression of
      C.EApp function argument -> collect function (argument : arguments)
      _ -> (expression, arguments)
    basisName expression = case locatedValue expression of
      C.EFfi "Basis" name -> Just name
      C.ECApp function _ -> basisName function
      _ -> Nothing

lowerShowIdentity :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerShowIdentity source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
      dictionary = at (M.TFun typ string)
  pure (at (M.EAbs "show" dictionary dictionary (at (M.ERel 0))))

lowerTransactionReturn :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerTransactionReturn source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      unit = State.unitType location
  pure (at (M.EAbs "value" typ (at (M.TFun unit typ))
    (at (M.EAbs "_" unit typ (at (M.ERel 1))))))

lowerTransactionBind :: C.Expr -> C.Con -> C.Con -> State.MonoM M.Expr
lowerTransactionBind source firstType resultType = do
  first <- State.monoType firstType
  result <- State.monoType resultType
  let location = locatedSpan source
      at = Located location
      unit = State.unitType location
      firstAction = at (M.TFun unit first)
      resultAction = at (M.TFun unit result)
      continuation = at (M.TFun first resultAction)
      runFirst = at (M.EApp (at (M.ERel 2)) (at (M.ERecord [])))
      runNext = at (M.EApp
        (at (M.EApp (at (M.ERel 2)) (at (M.ERel 0))))
        (at (M.ERecord [])))
      body = at (M.ELet "result" first runFirst runNext)
  pure (at (M.EAbs "first" firstAction (at (M.TFun continuation resultAction))
    (at (M.EAbs "continue" continuation resultAction
      (at (M.EAbs "_" unit result body))))))

lowerSource :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerSource source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      unit = State.unitType location
      sourceType = at M.TSource
      resultType = at (M.TFun unit sourceType)
      encoded = at (M.EJavaScript (M.JavaScriptSource typ) (at (M.ERel 1)))
      create = at (M.EFfiApp "Basis" "new_client_source" [] [(encoded, sourceType)])
  pure (at (M.EAbs "value" typ resultType
    (at (M.EAbs "_" unit sourceType create))))

lowerSetSource :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerSetSource source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      unit = State.unitType location
      sourceType = at M.TSource
      string = at (M.TFfi "Basis" "string")
      resultType = at (M.TFun typ (at (M.TFun unit unit)))
      encoded = at (M.EJavaScript (M.JavaScriptSource typ) (at (M.ERel 1)))
      update = at (M.EFfiApp "Basis" "set_client_source" []
        [(at (M.ERel 2), sourceType), (encoded, string)])
  pure (at (M.EAbs "source" sourceType resultType
    (at (M.EAbs "value" typ (at (M.TFun unit unit))
      (at (M.EAbs "_" unit unit update))))))

lowerGetSource :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerGetSource source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      unit = State.unitType location
      sourceType = at M.TSource
      resultType = at (M.TFun unit typ)
      getValue = at (M.EFfiApp "Basis" "get_client_source" []
        [(at (M.ERel 1), sourceType)])
  pure (at (M.EAbs "source" sourceType resultType
    (at (M.EAbs "_" unit typ getValue))))

lowerCurrentSignal :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerCurrentSignal source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      unit = State.unitType location
      sourceType = at M.TSource
      resultType = at (M.TFun unit typ)
      current = at (M.EFfiApp "Basis" "current" [] [(at (M.ERel 1), sourceType)])
  pure (at (M.EAbs "signal" sourceType resultType
    (at (M.EAbs "_" unit typ current))))

lowerSignalReturn :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerSignalReturn source valueType = do
  typ <- State.monoType valueType
  let at = Located (locatedSpan source)
  pure (at (M.EAbs "value" typ (at (M.TSignal typ))
    (at (M.ESignalReturn (at (M.ERel 0))))))

lowerSignalBind :: C.Expr -> C.Con -> C.Con -> State.MonoM M.Expr
lowerSignalBind source firstType resultType = do
  first <- State.monoType firstType
  result <- State.monoType resultType
  let location = locatedSpan source
      at = Located location
      firstSignal = at (M.TSignal first)
      resultSignal = at (M.TSignal result)
      continuation = at (M.TFun first resultSignal)
  pure (at (M.EAbs "signal" firstSignal (at (M.TFun continuation resultSignal))
    (at (M.EAbs "continue" continuation resultSignal
      (at (M.ESignalBind (at (M.ERel 1)) (at (M.ERel 0))))))))

lowerSignalSource :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerSignalSource source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      sourceType = at M.TSource
  pure (at (M.EAbs "source" sourceType (at (M.TSignal typ))
    (at (M.ESignalSource (at (M.ERel 0))))))

lowerEqSelector :: C.Expr -> C.Con -> Bool -> State.MonoM M.Expr
lowerEqSelector source valueType negateResult = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      bool = at (M.TFfi "Basis" "bool")
      equality = binaryFunctionType location typ bool
      applied = at (M.EApp
        (at (M.EApp (at (M.ERel 2)) (at (M.ERel 1))))
        (at (M.ERel 0)))
      body = if negateResult then at (M.EUnop "!" applied) else applied
  if negateResult
    then pure (at (M.EAbs "eq" equality equality
      (at (M.EAbs "left" typ (at (M.TFun typ bool))
        (at (M.EAbs "right" typ bool body))))))
    else pure (at (M.EAbs "eq" equality equality (at (M.ERel 0))))

comparisonFunctionValue :: C.Expr -> String -> M.BinopIntness -> String -> M.Expr
comparisonFunctionValue source typeName intness operator =
  curriedComparisonValue source typ
    (at (M.EBinop intness operator (at (M.ERel 1)) (at (M.ERel 0))))
  where
    at = Located (locatedSpan source)
    typ = at (M.TFfi "Basis" typeName)

timeComparisonFunctionValue :: C.Expr -> String -> M.Expr
timeComparisonFunctionValue source function =
  curriedComparisonValue source typ
    (at (M.EFfiApp "Basis" function []
      [(at (M.ERel 1), typ), (at (M.ERel 0), typ)]))
  where
    at = Located (locatedSpan source)
    typ = at (M.TFfi "Basis" "time")

curriedComparisonValue :: C.Expr -> M.Type -> M.Expr -> M.Expr
curriedComparisonValue source typ body =
  at (M.EAbs "left" typ (at (M.TFun typ bool))
    (at (M.EAbs "right" typ bool body)))
  where
    at = Located (locatedSpan source)
    bool = at (M.TFfi "Basis" "bool")

lowerOrderSelector :: C.Expr -> C.Con -> String -> Bool -> State.MonoM M.Expr
lowerOrderSelector source valueType field negateResult = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      bool = at (M.TFfi "Basis" "bool")
      comparison = binaryFunctionType location typ bool
      dictionary = orderDictionaryType location typ
      selected = at (M.EField (at (M.ERel 2)) (M.StaticName field))
      applied = at (M.EApp (at (M.EApp selected (at (M.ERel 1)))) (at (M.ERel 0)))
      body = if negateResult then at (M.EUnop "!" applied) else applied
  if negateResult
    then pure (at (M.EAbs "ord" dictionary comparison
      (at (M.EAbs "left" typ (at (M.TFun typ bool))
        (at (M.EAbs "right" typ bool body))))))
    else pure (at (M.EAbs "ord" dictionary comparison
      (at (M.EField (at (M.ERel 0)) (M.StaticName field)))))

lowerOrderIdentity :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerOrderIdentity source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      dictionary = orderDictionaryType location typ
  pure (at (M.EAbs "ord" dictionary dictionary (at (M.ERel 0))))

orderDictionaryValue :: C.Expr -> String -> M.BinopIntness -> M.Expr
orderDictionaryValue source typeName intness = at (M.ERecord
  [ (M.StaticName "Lt", comparison "<", comparisonType)
  , (M.StaticName "Le", comparison "<=", comparisonType)
  ])
  where
    location = locatedSpan source
    at = Located location
    typ = at (M.TFfi "Basis" typeName)
    bool = at (M.TFfi "Basis" "bool")
    comparisonType = binaryFunctionType location typ bool
    comparison operator = curriedComparisonValue source typ
      (at (M.EBinop intness operator (at (M.ERel 1)) (at (M.ERel 0))))

stringOrderDictionaryValue :: C.Expr -> M.Expr
stringOrderDictionaryValue source = at (M.ERecord
  [ (M.StaticName "Lt", comparison "<", comparisonType)
  , (M.StaticName "Le", comparison "<=", comparisonType)
  ])
  where
    location = locatedSpan source
    at = Located location
    typ = at (M.TFfi "Basis" "string")
    bool = at (M.TFfi "Basis" "bool")
    comparisonType = binaryFunctionType location typ bool
    comparison operator = curriedComparisonValue source typ
      (at (M.EBinop M.GeneralBinop operator
        (at (M.EBinop M.GeneralBinop "strcmp" (at (M.ERel 1)) (at (M.ERel 0))))
        (at (M.EPrim (PrimInt 0)))))

timeOrderDictionaryValue :: C.Expr -> M.Expr
timeOrderDictionaryValue source = at (M.ERecord
  [ (M.StaticName "Lt", timeComparisonFunctionValue source "lt_time", comparisonType)
  , (M.StaticName "Le", timeComparisonFunctionValue source "le_time", comparisonType)
  ])
  where
    location = locatedSpan source
    at = Located location
    typ = at (M.TFfi "Basis" "time")
    bool = at (M.TFfi "Basis" "bool")
    comparisonType = binaryFunctionType location typ bool

orderDictionaryType :: Span -> M.Type -> M.Type
orderDictionaryType location typ = at (M.TRecord
  [("Lt", comparison), ("Le", comparison)])
  where
    at = Located location
    bool = at (M.TFfi "Basis" "bool")
    comparison = binaryFunctionType location typ bool

lowerReadSelector :: C.Expr -> C.Con -> String -> State.MonoM M.Expr
lowerReadSelector source valueType field = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      (dictionary, reader, errorReader) = readTypes location typ
      result = if field == "Read" then reader else errorReader
  pure (at (M.EAbs "read" dictionary result
    (at (M.EField (at (M.ERel 0)) (M.StaticName field)))))

lowerMkRead :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerMkRead source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      (dictionary, reader, errorReader) = readTypes location typ
      body = at (M.ERecord
        [ (M.StaticName "Read", at (M.ERel 0), reader)
        , (M.StaticName "ReadError", at (M.ERel 1), errorReader)
        ])
  pure (at (M.EAbs "readError" errorReader (at (M.TFun reader dictionary))
    (at (M.EAbs "read" reader dictionary body))))

readDictionaryValue :: C.Expr -> String -> M.Expr
readDictionaryValue source typeName = at (M.ERecord
  [ (M.StaticName "Read", reader "stringTo" optional, readerType)
  , (M.StaticName "ReadError", reader "stringTo" typ, errorReaderType)
  ])
  where
    location = locatedSpan source
    at = Located location
    string = at (M.TFfi "Basis" "string")
    typ = at (M.TFfi "Basis" typeName)
    optional = at (M.TOption typ)
    readerType = at (M.TFun string optional)
    errorReaderType = at (M.TFun string typ)
    suffix = case typeName of
      "int" -> "Int"
      "float" -> "Float"
      "char" -> "Char"
      "bool" -> "Bool"
      _ -> "Time"
    reader prefix resultType = at (M.EAbs "value" string resultType
      (at (M.EFfiApp "Basis" (prefix <> suffix <> if resultType == typ then "_error" else "") []
        [(at (M.ERel 0), string)])))

stringReadDictionaryValue :: C.Expr -> M.Expr
stringReadDictionaryValue source = at (M.ERecord
  [ (M.StaticName "Read", at (M.EAbs "value" string optional
      (at (M.ESome string (at (M.ERel 0))))), readerType)
  , (M.StaticName "ReadError", at (M.EAbs "value" string string (at (M.ERel 0))), errorReaderType)
  ])
  where
    location = locatedSpan source
    at = Located location
    string = at (M.TFfi "Basis" "string")
    optional = at (M.TOption string)
    readerType = at (M.TFun string optional)
    errorReaderType = at (M.TFun string string)

readTypes :: Span -> M.Type -> (M.Type, M.Type, M.Type)
readTypes location typ = (dictionary, reader, errorReader)
  where
    at = Located location
    string = at (M.TFfi "Basis" "string")
    reader = at (M.TFun string (at (M.TOption typ)))
    errorReader = at (M.TFun string typ)
    dictionary = at (M.TRecord [("Read", reader), ("ReadError", errorReader)])

lowerNumericSelector :: C.Expr -> C.Con -> String -> State.MonoM M.Expr
lowerNumericSelector source valueType field = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      dictionary = numericDictionaryType location typ
      resultType = case field of
        "Zero" -> typ
        "Neg" -> at (M.TFun typ typ)
        _ -> binaryFunctionType location typ typ
  pure (at (M.EAbs "num" dictionary resultType
    (at (M.EField (at (M.ERel 0)) (M.StaticName field)))))

numericDictionaryValue
  :: C.Expr
  -> String
  -> M.BinopIntness
  -> Primitive
  -> [(String, String)]
  -> M.Expr
numericDictionaryValue source typeName intness zero operators =
  at (M.ERecord
    ( [ (M.StaticName "Zero", at (M.EPrim zero), typ)
      , (M.StaticName "Neg", unary "-", at (M.TFun typ typ))
      ]
      <> [ (M.StaticName field, binary operator, binaryType)
         | (field, operator) <- operators
         ]
    ))
  where
    location = locatedSpan source
    at = Located location
    typ = at (M.TFfi "Basis" typeName)
    binaryType = binaryFunctionType location typ typ
    unary operator = at (M.EAbs "value" typ typ
      (at (M.EUnop operator (at (M.ERel 0)))))
    binary operator = at (M.EAbs "left" typ (at (M.TFun typ typ))
      (at (M.EAbs "right" typ typ
        (at (M.EBinop intness operator (at (M.ERel 1)) (at (M.ERel 0)))))))

numericDictionaryType :: Span -> M.Type -> M.Type
numericDictionaryType location typ = at (M.TRecord
  [ ("Zero", typ)
  , ("Neg", at (M.TFun typ typ))
  , ("Plus", binary)
  , ("Minus", binary)
  , ("Times", binary)
  , ("Div", binary)
  , ("Mod", binary)
  , ("Pow", binary)
  ])
  where
    at = Located location
    binary = binaryFunctionType location typ typ

binaryFunctionType :: Span -> M.Type -> M.Type -> M.Type
binaryFunctionType location argument result =
  Located location (M.TFun argument (Located location (M.TFun argument result)))

lowerError :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerError source result = do
  resultType <- State.monoType result
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
  pure (at (M.EAbs "s" string resultType
    (at (M.EError (at (M.ERel 0)) resultType))))

lowerSerialize :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerSerialize source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
      value = at (M.ERel 0)
  encoded <- urlifyMono source value typ
  pure (at (M.EAbs "v" typ string encoded))

lowerDeserialize :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerDeserialize source valueType = do
  typ <- State.monoType valueType
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
  pure (at (M.EAbs "v" string typ (at (M.EUnurlify (at (M.ERel 0)) typ False))))

lowerSerializedIdentity :: C.Expr -> State.MonoM M.Expr
lowerSerializedIdentity source = do
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
  pure (at (M.EAbs "v" string string (at (M.ERel 0))))

lowerGetCookie :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerGetCookie source element = do
  elementType <- State.monoType element
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
      unit = State.unitType location
      optional = at (M.TOption elementType)
      raw = at (M.EFfiApp "Basis" "get_cookie" [] [(at (M.ERel 1), string)])
      body = at (M.EUnurlify raw elementType True)
  pure
    (at (M.EAbs "c" string (at (M.TFun unit optional))
      (at (M.EAbs "_" unit optional body))))

-- Ur turns these aborting response operations into explicit Mono nodes under
-- the transaction's unit thunk.  Keeping that shape here is important: it
-- prevents backends from mistaking redirect/returnBlob for ordinary FFI calls.
lowerRedirect :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerRedirect source result = do
  resultType <- State.monoType result
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
      unit = State.unitType location
  pure
    (at (M.EAbs "url" string (at (M.TFun unit resultType))
      (at (M.EAbs "_" unit resultType
        (at (M.ERedirect (at (M.ERel 1)) resultType))))))

lowerReturnBlob :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerReturnBlob source result = do
  resultType <- State.monoType result
  let location = locatedSpan source
      at = Located location
      blob = at (M.TFfi "Basis" "blob")
      string = at (M.TFfi "Basis" "string")
      unit = State.unitType location
  pure
    (at (M.EAbs "blob" blob
      (at (M.TFun string (at (M.TFun unit resultType))))
      (at (M.EAbs "mimeType" string (at (M.TFun unit resultType))
        (at (M.EAbs "_" unit resultType
          (at (M.EReturnBlob (Just (at (M.ERel 2))) (at (M.ERel 1)) resultType))))))))

textBlobReturn :: C.Expr -> C.Expr -> Maybe (C.Con, C.Expr)
textBlobReturn function argument = do
  resultType <- case locatedValue function of
    C.ECApp returnBlob result
      | C.EFfi "Basis" "returnBlob" <- locatedValue returnBlob -> Just result
    _ -> Nothing
  content <- case locatedValue argument of
    C.EFfiApp "Basis" "textBlob" [(value, _)] -> Just value
    C.EApp textBlob value
      | C.EFfi "Basis" "textBlob" <- locatedValue textBlob -> Just value
    _ -> Nothing
  pure (resultType, content)

lowerTextBlobReturn :: C.Expr -> C.Con -> C.Expr -> State.MonoM M.Expr
lowerTextBlobReturn source result content = do
  resultType <- State.monoType result
  content' <- monoExpr (Substitute.liftExprValues 0 2 content)
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
      unit = State.unitType location
      clear = at (M.EFfiApp "Basis" "clear_page" [] [])
      body = at (M.ESeq clear
        (at (M.ESeq (at (M.EWrite content'))
          (at (M.EReturnBlob Nothing (at (M.ERel 1)) resultType)))))
  pure (at (M.EAbs "mimeType" string (at (M.TFun unit resultType))
    (at (M.EAbs "_" unit resultType body))))

lowerSetCookie :: C.Expr -> C.Con -> State.MonoM M.Expr
lowerSetCookie source element = do
  elementType <- State.monoType element
  prefix <- State.getUrlPrefix
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
      bool = at (M.TFfi "Basis" "bool")
      time = at (M.TFfi "Basis" "time")
      unit = State.unitType location
      expiresType = at (M.TOption time)
      settingsType = at (M.TRecord
        [("Expires", expiresType), ("Secure", bool), ("Value", elementType)])
      settings = at (M.ERel 1)
      field name = at (M.EField settings (M.StaticName name))
  encoded <- urlifyMono source (field "Value") elementType
  let raw = at (M.EFfiApp "Basis" "set_cookie" []
        [ (at (M.EPrim (PrimString NormalString (ByteString.pack prefix))), string)
        , (at (M.ERel 2), string)
        , (encoded, string)
        , (field "Expires", expiresType)
        , (field "Secure", bool)
        ])
  pure
    (at (M.EAbs "c" string (at (M.TFun settingsType (at (M.TFun unit unit))))
      (at (M.EAbs "r" settingsType (at (M.TFun unit unit))
        (at (M.EAbs "_" unit unit raw))))))

lowerClearCookie :: C.Expr -> State.MonoM M.Expr
lowerClearCookie source = do
  prefix <- State.getUrlPrefix
  let location = locatedSpan source
      at = Located location
      string = at (M.TFfi "Basis" "string")
      unit = State.unitType location
      raw = at (M.EFfiApp "Basis" "clear_cookie" []
        [ (at (M.EPrim (PrimString NormalString (ByteString.pack prefix))), string)
        , (at (M.ERel 1), string)
        ])
  pure
    (at (M.EAbs "c" string (at (M.TFun unit unit))
      (at (M.EAbs "_" unit unit raw))))

urlifyMono :: C.Expr -> M.Expr -> M.Type -> State.MonoM M.Expr
urlifyMono source value typ = case locatedValue typ of
  M.TFfi "Basis" name
    | name `elem` ["string", "url", "css_class", "id"] -> primitive "urlifyString"
    | name == "int" -> primitive "urlifyInt"
    | name == "float" -> primitive "urlifyFloat"
    | name == "bool" -> primitive "urlifyBool"
    | name == "char" -> primitive "urlifyChar"
    | name == "time" -> primitive "urlifyTime"
    | name == "unit" -> pureText "_"
  M.TFfi moduleName typeName -> do
    allowed <- State.mayClientToServer moduleName typeName
    if allowed
      then pure (at (M.EFfiApp "Basis" "urlifyForeign"
        [M.StaticFfi moduleName typeName []] [(value, typ)]))
      else monoFailure source "urlify-type"
        ("Foreign type " <> moduleName <> "." <> typeName
          <> " has no clientToServer codec")
  M.TRecord [] -> pureText "_"
  M.TRecord (first : rest) -> do
    initial <- encodeField first
    foldM appendField initial rest
  M.TOption element -> do
    nested <- urlifyMono source (at (M.ERel 0)) element
    let nonePattern = at (M.PNone element)
        somePattern = at (M.PSome element (at (M.PVar "x" element)))
        resultType = string
    pure (at (M.ECase value
      [ (nonePattern, text "None")
      , (somePattern, at (M.EStrcat (text "Some/") nested))
      ] typ resultType))
  M.TList element -> urlifyList source value typ element
  M.TDatatype identifier -> urlifyDatatype source value typ identifier
  _ -> monoFailure source "urlify-type" "URL serialization for this monomorphic type is not implemented"
  where
    location = locatedSpan source
    at = Located location
    string = at (M.TFfi "Basis" "string")
    text bytes = at (M.EPrim (PrimString NormalString (ByteString.pack bytes)))
    pureText = pure . text
    primitive name = pure (at (M.EFfiApp "Basis" name [] [(value, typ)]))
    encodeField (name, fieldType) =
      urlifyMono source (at (M.EField value (M.StaticName name))) fieldType
    appendField encoded field = do
      next <- encodeField field
      pure (at (M.EStrcat encoded (at (M.EStrcat (text "/") next))))

urlifyList :: C.Expr -> M.Expr -> M.Type -> M.Type -> State.MonoM M.Expr
urlifyList source value listType element = do
  (identifier, fresh) <- State.reserveUrlifyHelper listType
  when fresh $ do
    let location = locatedSpan source
        at = Located location
        string = at (M.TFfi "Basis" "string")
        payloadType = listPayload location element
        payload = at (M.ERel 0)
        field name = at (M.EField payload (M.StaticName name))
        text bytes = at (M.EPrim (PrimString NormalString (ByteString.pack bytes)))
        nilPattern = at (M.PNone payloadType)
        consPattern = at (M.PSome payloadType (at (M.PVar "xs" payloadType)))
    headEncoded <- urlifyMono source (field "1") element
    let tailEncoded = at (M.EApp (at (M.ENamed identifier)) (field "2"))
        consEncoded = at (M.EStrcat (text "Cons/")
          (at (M.EStrcat headEncoded (at (M.EStrcat (text "/") tailEncoded)))))
        body = at (M.ECase (at (M.ERel 0))
          [(nilPattern, text "Nil"), (consPattern, consEncoded)] listType string)
        helperType = at (M.TFun listType string)
        helper = at (M.EAbs "xs" listType string body)
        declaration = at (M.DValRec [("$urlify_list", identifier, helperType, helper, "")])
    State.emitGeneratedValue declaration
  pure (Located (locatedSpan source) (M.EApp
    (Located (locatedSpan source) (M.ENamed identifier)) value))

urlifyDatatype :: C.Expr -> M.Expr -> M.Type -> M.GlobalId -> State.MonoM M.Expr
urlifyDatatype source value datatypeType datatypeIdentifier = do
  (identifier, fresh) <- State.reserveUrlifyHelper datatypeType
  when fresh $ do
    (classification, constructors) <- State.urlDatatypeConstructors datatypeIdentifier
    let location = locatedSpan source
        exprAt = Located location
        patternAt = Located location
        declAt = Located location
        typeAt = Located location
        string = typeAt (M.TFfi "Basis" "string")
        text bytes = exprAt (M.EPrim (PrimString NormalString (ByteString.pack bytes)))
    branches <- mapM (constructorBranch exprAt patternAt text classification) constructors
    let body = exprAt (M.ECase (exprAt (M.ERel 0)) branches datatypeType string)
        helperType = typeAt (M.TFun datatypeType string)
        helper = exprAt (M.EAbs "$urlify" datatypeType string body)
        declaration = declAt (M.DValRec [("$urlify_datatype", identifier, helperType, helper, "")])
    State.emitGeneratedValue declaration
  pure (Located (locatedSpan source) (M.EApp
    (Located (locatedSpan source) (M.ENamed identifier)) value))
  where
    constructorBranch exprAt patternAt text classification (name, constructor, payload) = case payload of
      Nothing -> pure
        ( patternAt (M.PCon classification (M.PConVar constructor) Nothing)
        , text name
        )
      Just payloadType -> do
        encoded <- urlifyMono source (exprAt (M.ERel 0)) payloadType
        pure
          ( patternAt (M.PCon classification (M.PConVar constructor)
              (Just (patternAt (M.PVar "x" payloadType))))
          , exprAt (M.EStrcat (text (name <> "/")) encoded)
          )

coreBasisApplication :: C.Expr -> Maybe (String, [C.Con])
coreBasisApplication = go []
  where
    go arguments expression = case locatedValue expression of
      C.ECApp function argument -> go (argument : arguments) function
      C.EFfi "Basis" name -> Just (name, arguments)
      _ -> Nothing

monoOption :: C.Expr -> C.PatCon -> [C.Con] -> Maybe C.Expr -> State.MonoM M.Expr
monoOption source constructor arguments payload = case arguments of
  [element] -> do
    elementType <- State.monoType element
    let payloadType = if isListConstructor constructor then listPayload (locatedSpan source) elementType else elementType
    case payload of
      Nothing -> pure (Located (locatedSpan source) (M.ENone payloadType))
      Just value -> Located (locatedSpan source) . M.ESome payloadType <$> monoExpr value
  _ -> do
    constructor' <- State.monoPatCon constructor arguments
    payload' <- traverse monoExpr payload
    pure (Located (locatedSpan source) (M.ECon C.Option constructor' payload'))

monoPattern :: C.Pattern -> State.MonoM M.Pattern
monoPattern source = case locatedValue source of
  C.PVar name typ -> Located (locatedSpan source) . M.PVar name <$> State.monoType typ
  C.PPrim primitive -> pure (Located (locatedSpan source) (M.PPrim primitive))
  C.PCon C.Option constructor arguments nested -> case arguments of
    [element] -> do
      elementType <- State.monoType element
      let payloadType = if isListConstructor constructor then listPayload (locatedSpan source) elementType else elementType
      case nested of
        Nothing -> pure (Located (locatedSpan source) (M.PNone payloadType))
        Just pattern' -> Located (locatedSpan source) . M.PSome payloadType <$> monoPattern pattern'
    _ -> ordinaryCon C.Option constructor arguments nested
  C.PCon classification constructor arguments nested -> ordinaryCon classification constructor arguments nested
  C.PRecord fields -> Located (locatedSpan source) . M.PRecord <$> mapM field fields
  where
    ordinaryCon classification constructor arguments nested =
      Located (locatedSpan source)
        <$> (M.PCon classification <$> State.monoPatCon constructor arguments <*> traverse monoPattern nested)
    field (name, nested, typ) = (,,) name <$> monoPattern nested <*> State.monoType typ

appendStatic :: C.Expr -> M.Expr -> M.StaticArg -> M.Expr
appendStatic source function argument = case locatedValue function of
  M.EFfi moduleName name arguments -> function {locatedValue = M.EFfi moduleName name (arguments <> [argument])}
  M.EFfiApp moduleName name arguments values -> function {locatedValue = M.EFfiApp moduleName name (arguments <> [argument]) values}
  _ -> Located (locatedSpan source) (M.EStaticApp function argument)

resolveStaticFfi :: C.Expr -> M.Expr -> M.Expr
resolveStaticFfi source expression = case locatedValue expression of
  M.EFfi "Basis" "show_xml" arguments | length arguments == 3 -> stringIdentity
  M.EFfi "Basis" "show_sql_query" arguments | length arguments == 4 -> stringIdentity
  _ -> expression
  where
    location = locatedSpan source
    at = Located location
    string = at (M.TFfi "Basis" "string")
    stringIdentity = at (M.EAbs "value" string string (at (M.ERel 0)))

-- Some Basis intrinsics take an ordinary dictionary/table argument between
-- static operands (for example sql_from_table).  The result is still a fully
-- resolved intrinsic application, even though the next static operand cannot
-- be stored directly on the EFfi node.
ffiHead :: M.Expr -> Bool
ffiHead expression = case locatedValue expression of
  M.EFfi {} -> True
  M.EFfiApp {} -> True
  M.EApp function _ -> ffiHead function
  M.EStaticApp function _ -> ffiHead function
  _ -> False

monoRow :: C.Con -> State.MonoM [(String, M.Type)]
monoRow source = case locatedValue (Substitute.normalizeCon source) of
  C.CRecord _ fields -> sortOn fst <$> mapM (\(name, typ) -> (,) <$> State.monoName name <*> State.monoType typ) fields
  _ -> monoFailure source "mono-row" "Schema row is not a concrete record"

monoRecordFieldName :: (M.StaticArg, M.Expr, M.Type) -> String
monoRecordFieldName (M.StaticName name, _, _) = name
monoRecordFieldName _ = ""

rowNames :: C.Con -> State.MonoM [M.StaticArg]
rowNames source = case locatedValue (Substitute.normalizeCon source) of
  C.CRecord _ fields -> mapM (State.monoStaticArg . fst) fields
  -- A Basis intrinsic may carry a closed row computation whose labels are not
  -- a literal record at this point.  Preserve that resolved computation as one
  -- descriptor instead of inventing field names.
  _ -> pure <$> State.monoStaticArg source

unwindExport :: C.Con -> ([C.Con], C.Con)
unwindExport typ = go (Substitute.normalizeCon typ) []
  where
    go current arguments = case locatedValue current of
      C.TFun domain range -> go (Substitute.normalizeCon range) (arguments <> [domain])
      C.CApp transaction result | isTransaction transaction -> go (Substitute.normalizeCon result) (arguments <> [unitCon (locatedSpan current)])
      _ -> (arguments, current)
    isTransaction constructor = case locatedValue (Substitute.normalizeCon constructor) of
      C.CFfi "Basis" "transaction" -> True
      _ -> False

unitCon :: Span -> C.Con
unitCon at = Located at (C.TRecord (Located at (C.CRecord (Located at C.KType) [])))

listPayload :: Span -> M.Type -> M.Type
listPayload at element = Located at (M.TRecord [("1", element), ("2", Located at (M.TList element))])

isListConstructor :: C.PatCon -> Bool
isListConstructor constructor = case constructor of
  C.PConFfi "Basis" "list" _ _ _ _ -> True
  _ -> False

collectValueInfo :: C.File -> ValueInfo
collectValueInfo = Map.fromList . concatMap collect
  where
    collect declaration = case locatedValue declaration of
      C.DVal _ identifier typ _ url -> [(identifier, (typ, url))]
      C.DValRec bindings -> [(identifier, (typ, url)) | (_, identifier, typ, _, url) <- bindings]
      _ -> []

collectSchemaNames :: C.File -> Map.Map C.GlobalId String
collectSchemaNames = Map.fromList . concatMap collect
  where
    collect declaration = case locatedValue declaration of
      C.DTable _ identifier _ physicalName _ _ _ _ -> [(identifier, physicalName)]
      C.DSequence _ identifier physicalName -> [(identifier, physicalName)]
      C.DView _ identifier physicalName _ _ -> [(identifier, physicalName)]
      _ -> []

runtimeValueIds :: [M.Decl] -> [M.GlobalId]
runtimeValueIds = concatMap collect
  where
    collect declaration = case locatedValue declaration of
      M.DVal _ identifier _ _ _ -> [identifier]
      M.DValRec bindings -> [identifier | (_, identifier, _, _, _) <- bindings]
      _ -> []

maximumGlobal :: C.File -> Int
maximumGlobal file = maximum (0 : concatMap collect file)
  where
    collect declaration = case locatedValue declaration of
      C.DCon _ identifier _ _ -> one identifier
      C.DDatatype definitions -> concat [[C.unGlobalId identifier] <> [C.unGlobalId constructor | (_, constructor, _) <- constructors] | (_, identifier, _, constructors) <- definitions]
      C.DVal _ identifier _ _ _ -> one identifier
      C.DValRec bindings -> [C.unGlobalId identifier | (_, identifier, _, _, _) <- bindings]
      C.DExport _ identifier _ -> one identifier
      C.DTable _ identifier _ _ _ _ _ _ -> one identifier
      C.DSequence _ identifier _ -> one identifier
      C.DView _ identifier _ _ _ -> one identifier
      C.DCookie _ identifier _ _ -> one identifier
      C.DStyle _ identifier _ -> one identifier
      C.DOnError identifier -> one identifier
      _ -> []
    one = pure . C.unGlobalId

monoFailure :: Located source -> String -> String -> State.MonoM value
monoFailure source code message =
  StateT (const (Left (diagnostic MonoPhase code (locatedSpan source) message)))
