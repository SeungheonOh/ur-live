{-# LANGUAGE DerivingStrategies #-}

-- | Direct JavaScript lowering from Vr's target-neutral Mono IR.  Generated
-- code uses ordinary JavaScript functions, closures, objects, promises, and
-- control flow; it does not reproduce Ur/Web's client-side CESK machine.
module Vr.Backend.JavaScript
  ( emitJavaScriptProject
  , emitJavaScriptProjectWithForeignAddon
  ) where

import Control.Monad (forM)
import Control.Monad.State.Strict (StateT (..), evalStateT, get, put)
import qualified Data.ByteString as ByteString
import Data.Char (ord)
import Data.List (intercalate, nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Numeric (showHex)
import qualified Vr.Backend.ClientJavaScript as Client
import qualified Vr.Backend.NodeAddon as NodeAddon
import qualified Vr.Mono.Server as Server
import qualified Vr.Mono.Syntax as M
import Vr.Middle (DbMode (..), Effect (..), ExportKind (..), FailureMode (..), Sidedness (..))
import Vr.Project
  ( FilterAction (..)
  , FilterKind (..)
  , FilterRule (..)
  , PatternKind (..)
  , ProjectAsset (..)
  , ProjectDirective (..)
  , ProjectPlan (..)
  , projectFilterRules
  )
import Vr.Source
  ( Diagnostic
  , DiagnosticPhase (BackendPhase)
  , Located (..)
  , Primitive (..)
  , StringMode (HtmlString)
  , diagnostic
  , noSpan
  )

data JavaScriptContext = JavaScriptContext
  { constructorTags :: !(Map.Map M.GlobalId Int)
  , foreignConstructors :: !(Map.Map (String, String, String) Server.ForeignConstructor)
  , clientHandlerIds :: !(Map.Map M.Expr Int)
  , clientHandlerCaptureIndices :: !(Map.Map M.Expr [Int])
  , clientDynamicIds :: !(Map.Map M.Expr Int)
  , clientDynamicCaptureIndices :: !(Map.Map M.Expr [Int])
  , clientActiveIds :: !(Map.Map M.Expr Int)
  , clientActiveCaptureIndices :: !(Map.Map M.Expr [Int])
  , clientClosureIds :: !(Map.Map M.Expr Int)
  , clientClosureCaptureIndices :: !(Map.Map M.Expr [Int])
  , foreignBindings :: !(Map.Map Server.ForeignName NodeAddon.ForeignBinding)
  , foreignTagNames :: !(Set.Set Server.ForeignName)
  , serverDefinitionIds :: !(Set.Set M.GlobalId)
  }

data GenerateState = GenerateState
  { nextVariable :: !Int
  , stringLiterals :: !(Map.Map ByteString.ByteString (Int, Bool, Bool))
  }

type Generate = StateT GenerateState (Either Diagnostic)

-- | Emit an ordinary ECMAScript module.  @runtimeImport@ is written verbatim
-- as the module specifier for Vr's runtime; the CLI places that runtime beside
-- the generated application.
emitJavaScriptProject
  :: String
  -> ProjectPlan
  -> [ProjectAsset]
  -> [String]
  -> M.File
  -> Either [Diagnostic] String
emitJavaScriptProject runtimeImport plan assets javascriptFiles file =
  emitJavaScriptProjectInternal runtimeImport Nothing plan assets javascriptFiles file

-- | Emit a server module that loads a generated Node N-API sidecar whenever
-- reachable custom C foreign values are present.
emitJavaScriptProjectWithForeignAddon
  :: String
  -> String
  -> ProjectPlan
  -> [ProjectAsset]
  -> [String]
  -> M.File
  -> Either [Diagnostic] String
emitJavaScriptProjectWithForeignAddon runtimeImport addonImport plan assets javascriptFiles file =
  emitJavaScriptProjectInternal runtimeImport (Just addonImport) plan assets javascriptFiles file

emitJavaScriptProjectInternal
  :: String
  -> Maybe String
  -> ProjectPlan
  -> [ProjectAsset]
  -> [String]
  -> M.File
  -> Either [Diagnostic] String
emitJavaScriptProjectInternal runtimeImport addonImport plan assets javascriptFiles monoFile = do
  case unsupportedLimits of
    [] -> Right ()
    directives -> Left
      [ diagnostic BackendPhase "javascript-limit" (projectDirectiveSpan directive)
          "The direct-JavaScript backend does not yet implement this resource-limit category"
      | directive <- directives
      ]
  case Server.serverSideProblems plan file of
    [] -> Right ()
    problems -> Left problems
  bindings <- NodeAddon.collectForeignBindings plan file
  let codecs = NodeAddon.collectForeignCodecs plan
      constructors = Server.serverForeignConstructors plan file
  case (not (null bindings) || not (null codecs) || not (null constructors), addonImport) of
    (True, Nothing) -> Left
      [diagnostic BackendPhase "javascript-ffi-sidecar" noSpan
        "This application needs the generated native FFI sidecar"]
    _ -> Right ()
  case evalStateT (renderModule runtimeImport addonImport bindings plan assets javascriptFiles file)
      (GenerateState 0 Map.empty) of
    Left problem -> Left [problem]
    Right output -> Right output
  where
    file = monoFile
    unsupportedLimits =
      [ directive
      | directive <- projectDirectives plan
      , projectDirectiveName directive == "limit"
      , case words (projectDirectiveArgument directive) of
          [kind, _] -> kind `notElem`
            ["inputs", "clients", "headers", "page", "heap", "script", "subinputs", "cleanup", "messages", "deltas", "transactionals", "globals", "database", "time"]
          _ -> True
      ]

renderModule
  :: String
  -> Maybe String
  -> [NodeAddon.ForeignBinding]
  -> ProjectPlan
  -> [ProjectAsset]
  -> [String]
  -> M.File
  -> Generate String
renderModule runtimeImport addonImport bindings plan assets javascriptFiles file = do
  client <- liftEither (Client.compileClientProgram plan javascriptFiles file)
  let declarations = M.fileDeclarations file
      codecs = NodeAddon.collectForeignCodecs plan
      reachable = Server.serverReachableDefinitionIds plan file
      context = JavaScriptContext
        { constructorTags = collectConstructorTags declarations
        , foreignConstructors = Map.fromList
            [ ( ( Server.foreignConstructorModule constructor
                , Server.foreignConstructorDatatype constructor
                , Server.foreignConstructorName constructor
                )
              , constructor
              )
            | constructor <- Server.serverForeignConstructors plan file
            ]
        , clientHandlerIds = Client.clientHandlers client
        , clientHandlerCaptureIndices = Client.clientHandlerCaptures client
        , clientDynamicIds = Client.clientDynamics client
        , clientDynamicCaptureIndices = Client.clientDynamicCaptures client
        , clientActiveIds = Client.clientActives client
        , clientActiveCaptureIndices = Client.clientActiveCaptures client
        , clientClosureIds = Client.clientClosures client
        , clientClosureCaptureIndices = Client.clientClosureCaptures client
        , foreignBindings = Map.fromList
            [ ((NodeAddon.foreignBindingModule binding, NodeAddon.foreignBindingMember binding), binding)
            | binding <- bindings
            ]
        , foreignTagNames = Server.foreignHtmlTagNames file
        , serverDefinitionIds = reachable
        }
      globals = nub (filter (`Set.member` reachable) (collectGlobals declarations))
      declarationLines = map (\identifier -> "let " <> globalName identifier <> ";") globals
  assignments <- fmap concat (mapM (renderDeclaration context) declarations)
  tasks <- fmap concat (mapM (renderTask context) declarations)
  routes <- fmap concat (mapM renderRoute declarations)
  tables <- fmap concat (mapM (renderTable context) declarations)
  views <- fmap concat (mapM (renderView context) declarations)
  indexes <- fmap concat (mapM renderIndex declarations)
  onError <- renderOnError declarations
  generated <- get
  let assetValues = map renderAsset assets
      literalLines = concat
        [ ["const " <> pooledLiteralName identifier <> " = " <> decoded <> ";" | usedAsString]
          <> ["const " <> pooledHtmlLiteralName identifier <> " = vr.literalHtml("
                <> (if usedAsString then pooledLiteralName identifier else decoded) <> ");" | usedAsHtml]
        | (bytes, (identifier, usedAsString, usedAsHtml)) <- Map.toAscList (stringLiterals generated)
        , let decoded = "vr.bytes(" <> quoteString (hexBytes bytes) <> ")"
        ]
      datatypeValues = concatMap renderDatatypes declarations
      databases = [quoteString connection | declaration <- declarations, M.DDatabaseRaw connection <- [locatedValue declaration]]
      sequences = [quoteString name | declaration <- declarations, M.DSequence name <- [locatedValue declaration]]
      cookies = [quoteString name | declaration <- declarations, M.DCookie name <- [locatedValue declaration]]
      environment = map quoteString (collectXsrfEnvironment plan declarations)
      modes = map renderFunctionMode (M.fileFunctionModes file)
      directives = map renderDirective (projectDirectives plan)
      filters = map renderFilterRule (projectFilterRules plan)
      application =
        [ "await vr.start({"
        , "  routes: [" <> intercalate ",\n    " routes <> "],"
        , "  datatypes: [" <> intercalate ",\n    " datatypeValues <> "],"
        , "  database: " <> (case reverse databases of value : _ -> value; [] -> "null") <> ","
        , "  tables: [" <> intercalate ",\n    " tables <> "],"
        , "  views: [" <> intercalate ",\n    " views <> "],"
        , "  indexes: [" <> intercalate ",\n    " indexes <> "],"
        , "  sequences: [" <> intercalate ", " sequences <> "],"
        , "  cookies: [" <> intercalate ", " cookies <> "],"
        , "  environment: [" <> intercalate ", " environment <> "],"
        , "  assets: [" <> intercalate ",\n    " assetValues <> "],"
        , "  tasks: [" <> intercalate ",\n    " tasks <> "],"
        , "  functionModes: [" <> intercalate ", " modes <> "],"
        , "  clientScript: " <> quoteString (Client.clientScript client) <> ","
        , "  onError: " <> onError
        , "});"
        ]
      foreignSetup = case addonImport of
        Just path ->
          [ "import { createRequire } from \"node:module\";"
          , "const vrForeign = createRequire(import.meta.url)(" <> quoteString path <> ");"
          ]
        _ -> []
      foreignConfiguration = case addonImport of
        Just _ -> ", foreign: vrForeign, foreignCodecs: ["
          <> intercalate ", " (map renderForeignCodec codecs) <> "]"
          <> ", foreignTransactions: " <> jsBool
            (not (null bindings) || not (null codecs)
              || not (Map.null (foreignConstructors context)))
        Nothing -> ""
  pure $ unlines
    ( [ "// Generated by Vr's direct JavaScript backend."
      , "import { createRuntime } from " <> quoteString runtimeImport <> ";"
      ]
        <> foreignSetup
        <> [ ""
           , "const vr = createRuntime({ directives: [" <> intercalate ", " directives <> "]"
               <> ", filters: [" <> intercalate ", " filters <> "]"
               <> foreignConfiguration <> " });"
           ]
        <> literalLines
        <> declarationLines
        <> [""]
        <> assignments
        <> [""]
        <> application
    )

renderForeignCodec :: NodeAddon.ForeignCodec -> String
renderForeignCodec codec =
  "{ id: " <> show (NodeAddon.foreignCodecId codec)
    <> ", module: " <> quoteString (NodeAddon.foreignCodecModule codec)
    <> ", name: " <> quoteString (NodeAddon.foreignCodecType codec) <> " }"

renderFilterRule :: FilterRule -> String
renderFilterRule rule =
  "{ kind: " <> quoteString (kindName (filterRuleKind rule))
    <> ", allow: " <> jsBool (filterRuleAction rule == FilterAllow)
    <> ", prefix: " <> jsBool (filterRulePatternKind rule == PrefixPattern)
    <> ", pattern: " <> quoteString (filterRulePattern rule) <> " }"
  where
    kindName kind = case kind of
      FilterUrl -> "url"
      FilterMime -> "mime"
      FilterRequestHeader -> "requestHeader"
      FilterResponseHeader -> "responseHeader"
      FilterEnv -> "env"
      FilterMeta -> "meta"

renderDeclaration :: JavaScriptContext -> M.Decl -> Generate [String]
renderDeclaration context declaration = case locatedValue declaration of
  M.DVal _ identifier _ expression _ | Set.member identifier (serverDefinitionIds context) -> do
    value <- renderExpr context [] expression
    pure [globalName identifier <> " = " <> value <> ";"]
  M.DValRec bindings -> forM bindings $ \(_, identifier, _, expression, _) -> do
    if Set.member identifier (serverDefinitionIds context)
      then do
        value <- renderRecursiveValue context identifier expression
        pure (globalName identifier <> " = vr.deadline(" <> value <> ", "
          <> show (functionArity expression) <> ");")
      else pure ""
  _ -> pure []

functionArity :: M.Expr -> Int
functionArity expression = case locatedValue expression of
  M.EAbs _ _ _ body -> 1 + functionArity body
  _ -> 0

-- | Render self calls in tail position as a local loop.  JavaScript engines
-- do not implement proper tail calls consistently, while Ur programs quite
-- commonly use accumulator-style recursion.  Only exact, fully applied calls
-- to the binding currently being emitted are rewritten; partial,
-- over-applied, non-tail, and mutually recursive calls keep the ordinary
-- application path.
renderRecursiveValue :: JavaScriptContext -> M.GlobalId -> M.Expr -> Generate String
renderRecursiveValue context identifier expression = do
  let (abstractions, body) = collectAbstractions expression
  parameters <- mapM (const (freshName "argument")) abstractions
  let locals = reverse parameters
  (body', optimized) <- renderTailExpression context identifier parameters locals body
  if null parameters || not optimized
    then renderExpr context [] expression
    else pure (renderCurriedLoop parameters body')

collectAbstractions :: M.Expr -> ([M.Expr], M.Expr)
collectAbstractions expression = case locatedValue expression of
  M.EAbs _ _ _ body ->
    let (nested, result) = collectAbstractions body
     in (expression : nested, result)
  _ -> ([], expression)

renderCurriedLoop :: [String] -> String -> String
renderCurriedLoop parameters body = case parameters of
  [] -> "() => { while (true) { " <> body <> " } }"
  [parameter] -> "(" <> parameter <> ") => { while (true) { " <> body <> " } }"
  parameter : rest -> "(" <> parameter <> ") => " <> renderCurriedLoop rest body

renderTailExpression
  :: JavaScriptContext
  -> M.GlobalId
  -> [String]
  -> [String]
  -> M.Expr
  -> Generate (String, Bool)
renderTailExpression context identifier parameters locals expression =
  case collectApplications expression of
    (function, arguments)
      | M.ENamed called <- locatedValue function
      , called == identifier
      , length arguments == length parameters -> do
          arguments' <- mapM (renderExpr context locals) arguments
          temporaries <- mapM (const (freshName "tail")) arguments
          let evaluate = concat
                [ "const " <> temporary <> " = " <> argument <> "; "
                | (temporary, argument) <- zip temporaries arguments'
                ]
              assign = concat
                [ parameter <> " = " <> temporary <> "; "
                | (parameter, temporary) <- zip parameters temporaries
                ]
          pure (evaluate <> "vr.checkDeadline(); " <> assign <> "continue;", True)
    _ -> case locatedValue expression of
      M.ECase scrutinee branches _ _ -> do
        scrutineeName <- freshName "scrutinee"
        scrutinee' <- renderExpr context locals scrutinee
        rendered <- mapM (renderTailBranch context identifier parameters locals scrutineeName) branches
        let optimized = or (map snd rendered)
            branchLines = concatMap fst rendered
        pure
          ( "const " <> scrutineeName <> " = vr.force(" <> scrutinee' <> "); "
              <> branchLines <> "return vr.matchFailure();"
          , optimized
          )
      _ -> do
        value <- renderExpr context locals expression
        pure ("return " <> value <> ";", False)

renderTailBranch
  :: JavaScriptContext
  -> M.GlobalId
  -> [String]
  -> [String]
  -> String
  -> (M.Pattern, M.Expr)
  -> Generate (String, Bool)
renderTailBranch context identifier parameters locals value (pattern', body) = do
  plan <- renderPattern context value pattern'
  let names = map fst (patternBindings plan)
      declarations = concat
        ["const " <> name <> " = " <> source <> "; " | (name, source) <- patternBindings plan]
  (body', optimized) <-
    renderTailExpression context identifier parameters (reverse names <> locals) body
  pure
    ( "if (" <> patternTest plan <> ") { " <> declarations <> body' <> " } "
    , optimized
    )

renderTask :: JavaScriptContext -> M.Decl -> Generate [String]
renderTask context declaration = case locatedValue declaration of
  M.DTask schedule body -> do
    schedule' <- renderExpr context [] schedule
    body' <- renderExpr context [] body
    pure ["{ schedule: " <> schedule' <> ", body: " <> body' <> " }"]
  _ -> pure []

renderRoute :: M.Decl -> Generate [String]
renderRoute declaration = case locatedValue declaration of
  M.DExport kind path identifier arguments result pageNeedsSignature -> do
    -- The last argument starts the exported transaction and is supplied as
    -- unit by the runtime.  Only the preceding arguments belong to the URL
    -- or submitted form, matching the native backend's endpoint lowering.
    let arity = max 0 (length arguments - 1)
    pure
      [ "{ kind: " <> quoteString (exportKindName kind)
          <> ", effect: " <> quoteString (exportEffectName kind)
          <> ", path: " <> quoteString (leadingSlash path)
          <> ", identifier: " <> show (M.unGlobalId identifier)
          <> ", handler: " <> globalName identifier
          <> ", arity: " <> show arity
          <> ", arguments: [" <> intercalate ", " (map renderType (take arity arguments)) <> "]"
          <> ", result: " <> renderType result
          <> ", pageNeedsSignature: " <> jsBool pageNeedsSignature <> " }"
      ]
  _ -> pure []

renderTable :: JavaScriptContext -> M.Decl -> Generate [String]
renderTable context declaration = case locatedValue declaration of
  M.DTable name fields primary constraints -> do
    primary' <- renderExpr context [] primary
    constraints' <- renderExpr context [] constraints
    pure
      [ "{ name: " <> quoteString name
          <> ", fields: [" <> intercalate ", "
            ["[" <> quoteString field <> ", " <> renderType typ <> "]" | (field, typ) <- fields]
          <> "], primary: " <> primary' <> ", constraints: " <> constraints' <> " }"
      ]
  _ -> pure []

renderView :: JavaScriptContext -> M.Decl -> Generate [String]
renderView context declaration = case locatedValue declaration of
  M.DView name fields query -> do
    query' <- renderExpr context [] query
    pure
      [ "{ name: " <> quoteString name
          <> ", fields: [" <> intercalate ", "
            ["[" <> quoteString field <> ", " <> renderType typ <> "]" | (field, typ) <- fields]
          <> "], query: " <> query' <> " }"
      ]
  _ -> pure []

renderIndex :: M.Decl -> Generate [String]
renderIndex declaration = case locatedValue declaration of
  M.DIndex table modes -> pure
    [ "{ table: " <> quoteString table <> ", fields: ["
        <> intercalate ", "
          [ "[" <> quoteString field <> ", " <> quoteString (indexModeName mode) <> "]"
          | (field, mode) <- modes
          , mode /= M.IndexSkipped
          ]
        <> "] }"
    | any ((/= M.IndexSkipped) . snd) modes
    ]
  M.DIndexDynamic {} -> backendFailure declaration "javascript-index"
    "A dynamic database index survived monomorphic lowering"
  _ -> pure []
  where
    indexModeName mode = case mode of
      M.IndexEquality -> "equality"
      M.IndexTrigram -> "trigram"
      M.IndexSkipped -> "skipped"

renderOnError :: [M.Decl] -> Generate String
renderOnError declarations = pure $ case
  [globalName identifier | declaration <- declarations, M.DOnError identifier <- [locatedValue declaration]] of
    [] -> "null"
    handlers -> last handlers

renderAsset :: ProjectAsset -> String
renderAsset asset =
  "{ path: " <> quoteString (leadingSlash (bytesAsChars (projectAssetUri asset)))
    <> ", mime: " <> quoteString (bytesAsChars (projectAssetMime asset))
    <> ", hex: " <> quoteString (hexBytes (projectAssetBytes asset)) <> " }"

-- Constructor names are part of Ur/Web's stable URL/RPC wire format, while
-- runtime values use compact numeric tags.  Emit both views once so every
-- transport can marshal structural values without backend-specific guesses.
renderDatatypes :: M.Decl -> [String]
renderDatatypes declaration = case locatedValue declaration of
  M.DDatatype definitions -> map renderDatatype definitions
  _ -> []
  where
    renderDatatype (name, identifier, constructors) =
      "{ name: " <> quoteString name
        <> ", id: " <> show (M.unGlobalId identifier)
        <> ", constructors: [" <> intercalate ", "
          [ "{ name: " <> quoteString constructorName
              <> ", id: " <> show (M.unGlobalId constructorIdentifier)
              <> ", tag: " <> show tag
              <> ", payload: " <> maybe "null" renderType payload <> " }"
          | (tag, (constructorName, constructorIdentifier, payload)) <- zip [0 :: Int ..] constructors
          ]
        <> "] }"

renderDirective :: ProjectDirective -> String
renderDirective directive =
  "{ name: " <> quoteString (projectDirectiveName directive)
    <> ", argument: " <> quoteString (projectDirectiveArgument directive) <> " }"

renderFunctionMode :: (M.GlobalId, Sidedness, DbMode) -> String
renderFunctionMode (identifier, placement, databaseMode) =
  "[" <> show (M.unGlobalId identifier) <> ", " <> quoteString (sidednessName placement)
    <> ", " <> quoteString (databaseModeName databaseMode) <> "]"

renderExpr :: JavaScriptContext -> [String] -> M.Expr -> Generate String
renderExpr context locals source = case locatedValue source of
  M.EPrim primitive -> renderPrimitive primitive
  M.ERel index -> case drop index locals of
    name : _ -> pure name
    [] -> backendFailure source "javascript-local" ("Invalid local index " <> show index)
  M.ENamed identifier -> pure (globalName identifier)
  M.ECon _ constructor payload -> renderConstructor context locals constructor payload
  M.ENone _ -> pure "({ tag: 0, payload: null })"
  M.ESome _ value -> do
    value' <- renderExpr context locals value
    pure ("({ tag: 1, payload: " <> value' <> " })")
  M.EFfi "Basis" name staticArguments ->
    pure ("vr.basis(" <> quoteString name <> ", "
      <> renderStaticList (runtimeBasisArguments name staticArguments) <> ")")
  M.EFfi moduleName name staticArguments
    | Set.member (moduleName, name) (foreignTagNames context) ->
        pure (renderBasis name staticArguments [])
  M.EFfi moduleName name _ -> renderForeign context source moduleName name []
  M.EFfiApp "Basis" "tag" staticArguments arguments
    | [classes, dynamicClass, style, dynamicStyle, attributes, descriptor, child] <- map fst arguments ->
        renderTagApplication context locals staticArguments
          classes dynamicClass style dynamicStyle attributes descriptor child
  M.EFfiApp "Basis" "__vr_tag_open" staticArguments arguments
    | [classes, dynamicClass, style, dynamicStyle, attributes, descriptor] <- map fst arguments ->
        renderTagOpeningApplication context locals staticArguments
          classes dynamicClass style dynamicStyle attributes descriptor
  M.EFfiApp "Basis" name staticArguments arguments -> do
    arguments' <- mapM (renderExpr context locals . fst) arguments
    pure (renderBasis name staticArguments arguments')
  M.EFfiApp moduleName name staticArguments arguments
    | Set.member (moduleName, name) (foreignTagNames context) -> do
        arguments' <- mapM (renderExpr context locals . fst) arguments
        pure (renderBasis name staticArguments arguments')
  M.EFfiApp moduleName name _ arguments -> do
    arguments' <- mapM (renderExpr context locals . fst) arguments
    renderForeign context source moduleName name arguments'
  M.EApp {} -> renderApplication context locals source
  M.EAbs _ _ _ body -> do
    parameter <- freshName "argument"
    body' <- renderExpr context (parameter : locals) body
    let functionValue = "(" <> parameter <> ") => " <> body'
    case Map.lookup source (clientClosureIds context) of
      Nothing -> pure functionValue
      Just identifier -> do
        let captureAt index = case drop index locals of
              capture : _ -> pure capture
              [] -> backendFailure source "javascript-client-closure"
                ("Browser closure refers to unavailable local " <> show index)
        captures <- mapM captureAt
          (Map.findWithDefault [] source (clientClosureCaptureIndices context))
        pure ("vr.clientClosure(" <> show identifier <> ", ["
          <> intercalate ", " captures <> "], " <> functionValue <> ")")
  M.EStaticApp function argument -> do
    function' <- renderExpr context locals function
    pure ("vr.staticApp(" <> function' <> ", " <> renderStatic argument <> ")")
  M.EUnop operator value -> do
    value' <- renderExpr context locals value
    pure $ if operator == "!"
      then "(!vr.force(" <> value' <> "))"
      else "vr.force(" <> renderBasis operator [] [value'] <> ")"
  M.EBinop intness operator left right -> do
    left' <- renderExpr context locals left
    right' <- renderExpr context locals right
    pure $ case intness of
      M.IntegerBinop ->
        renderIntegerBinary operator left' right'
      M.GeneralBinop -> renderGeneralBinary operator left' right'
  M.ERecord fields -> do
    fields' <- mapM (renderField context locals source) fields
    pure ("({ " <> intercalate ", " fields' <> " })")
  M.EField record field -> do
    record' <- renderExpr context locals record
    name <- staticName source field
    pure ("vr.force(" <> record' <> ")[" <> quoteString name <> "]")
  M.ERecordConcat left right -> do
    left' <- renderExpr context locals left
    right' <- renderExpr context locals right
    pure ("({ ...vr.force(" <> left' <> "), ...vr.force(" <> right' <> ") })")
  M.ERecordCut record fields -> do
    record' <- renderExpr context locals record
    names <- mapM (staticName source) fields
    pure ("vr.recordCut(" <> record' <> ", [" <> intercalate ", " (map quoteString names) <> "])")
  M.ECase scrutinee branches _ _ -> renderCase context locals source scrutinee branches
  M.EStrcat left right -> do
    left' <- renderExpr context locals left
    right' <- renderExpr context locals right
    pure ("vr.concat(" <> left' <> ", " <> right' <> ")")
  M.EError message _ -> do
    message' <- renderExpr context locals message
    pure ("vr.fail(" <> message' <> ")")
  M.EReturnBlob blob mimeType _ -> do
    blob' <- maybe (pure "null") (renderExpr context locals) blob
    mimeType' <- renderExpr context locals mimeType
    pure ("vr.returnBlobNow(" <> blob' <> ", " <> mimeType' <> ")")
  M.ERedirect value _ -> do
    value' <- renderExpr context locals value
    pure ("vr.redirectNow(" <> value' <> ")")
  M.EWrite value | Just integer <- Server.integerHtmlArgument value -> do
    integer' <- renderExpr context locals integer
    pure ("vr.writeInt(" <> integer' <> ")")
  M.EWrite value -> do
    value' <- renderExpr context locals value
    pure ("vr.write(" <> value' <> ")")
  M.ESeq first second -> do
    first' <- renderExpr context locals first
    second' <- renderExpr context locals second
    pure $ if immediateWrite first
      then "(" <> first' <> ", " <> second' <> ")"
      else "vr.sequence(" <> first' <> ", () => " <> second' <> ")"
  M.ELet _ _ value body -> do
    variable <- freshName "local"
    value' <- renderExpr context locals value
    body' <- renderExpr context (variable : locals) body
    pure ("vr.letValue(" <> value' <> ", (" <> variable <> ") => " <> body' <> ")")
  M.EClosure identifier captures -> do
    captures' <- mapM (renderExpr context locals) captures
    pure
      ("vr.closure(" <> show (M.unGlobalId identifier) <> ", " <> globalName identifier
        <> ", [" <> intercalate ", " captures' <> "])")
  M.EQuery fields tables state query body initial -> do
    query' <- renderExpr context locals query
    body' <- renderExpr context locals body
    initial' <- renderExpr context locals initial
    pure
      ("vr.query(" <> renderQueryShape fields tables state <> ", " <> query' <> ", "
        <> body' <> ", " <> initial' <> ")")
  M.EDml value failure -> do
    value' <- renderExpr context locals value
    pure ("vr.dml(" <> value' <> ", " <> quoteString (failureModeName failure) <> ")")
  M.ENextval value -> do
    value' <- renderExpr context locals value
    pure ("vr.nextval(" <> value' <> ")")
  M.ESetval sequence' value -> do
    sequence'' <- renderExpr context locals sequence'
    value' <- renderExpr context locals value
    pure ("vr.setval(" <> sequence'' <> ", " <> value' <> ")")
  M.EUnurlify value typ optional -> do
    value' <- renderExpr context locals value
    pure ("vr.unurlify(" <> value' <> ", " <> renderType typ <> ", " <> jsBool optional <> ")")
  M.EJavaScript mode value -> do
    value' <- renderExpr context locals value
    pure ("vr.javascript(" <> quoteString (javaScriptModeName mode) <> ", " <> value' <> ")")
  M.ESignalReturn value -> do
    value' <- renderExpr context locals value
    pure ("vr.signalReturn(" <> value' <> ")")
  M.ESignalBind signal continuation -> do
    signal' <- renderExpr context locals signal
    continuation' <- renderExpr context locals continuation
    pure ("vr.signalBind(" <> signal' <> ", " <> continuation' <> ")")
  M.ESignalSource value -> do
    value' <- renderExpr context locals value
    pure ("vr.signalSource(" <> value' <> ")")
  M.EServerCall call typ effect failure -> do
    call' <- renderExpr context locals call
    pure
      ("vr.serverCall(" <> call' <> ", " <> renderType typ <> ", "
        <> quoteString (effectName effect) <> ", " <> quoteString (failureModeName failure) <> ")")
  M.ERecv channel _ -> do
    channel' <- renderExpr context locals channel
    pure (renderBasis "recv" [] [channel'])
  M.ESleep value -> do
    value' <- renderExpr context locals value
    pure ("vr.sleep(" <> value' <> ")")
  M.ESpawn value -> do
    value' <- renderExpr context locals value
    pure ("vr.spawn(" <> value' <> ")")
  M.ESqlCache index typ keys action -> do
    keys' <- mapM (renderExpr context locals) keys
    action' <- renderExpr context locals action
    let operation = if bareSqlQuery action then "sqlCache" else "sqlCacheDirect"
    pure
      ("vr." <> operation <> "(" <> show index <> ", [" <> intercalate ", " keys'
        <> "], " <> renderType typ <> ", () => " <> action' <> ")")
  M.ESqlCacheFlush _ flushes action -> do
    flushes' <- mapM renderFlush flushes
    action' <- renderExpr context locals action
    pure ("vr.sqlCacheFlush([" <> intercalate ", " flushes' <> "], " <> action' <> ")")
    where
      renderFlush flush = do
        keys <- mapM (traverse (renderExpr context locals)) (M.sqlCacheFlushKeys flush)
        pure
          ("{ index: " <> show (M.sqlCacheFlushIndex flush) <> ", keys: ["
            <> intercalate ", " (map (maybe "null" id) keys) <> "] }")

bareSqlQuery :: M.Expr -> Bool
bareSqlQuery expression = case locatedValue expression of
  M.EQuery {} -> True
  _ -> case collectApplications expression of
    (headExpression, [_, _, _]) -> case locatedValue headExpression of
      M.EFfi "Basis" "query" _ -> True
      M.EFfiApp "Basis" "query" _ [] -> True
      _ -> False
    _ -> False

renderApplication :: JavaScriptContext -> [String] -> M.Expr -> Generate String
renderApplication context locals source = do
  let (function, arguments) = collectApplications source
  case locatedValue function of
    M.EFfi "Basis" "tag" staticArguments
      | [classes, dynamicClass, style, dynamicStyle, attributes, descriptor, child] <- arguments ->
          renderTagApplication context locals staticArguments
            classes dynamicClass style dynamicStyle attributes descriptor child
    M.EFfi "Basis" "__vr_tag_open" staticArguments
      | [classes, dynamicClass, style, dynamicStyle, attributes, descriptor] <- arguments ->
          renderTagOpeningApplication context locals staticArguments
            classes dynamicClass style dynamicStyle attributes descriptor
    M.EFfi "Basis" "cdata" _ | [argument] <- arguments ->
      if htmlSafeExpression argument
        then renderExpr context locals argument
        else do
          argument' <- renderExpr context locals argument
          pure ("vr.htmlEscape(" <> argument' <> ")")
    M.EFfi "Basis" name staticArguments -> do
      arguments' <- mapM (renderExpr context locals) arguments
      case basisTransactionArity name of
        Just arity | length arguments' > arity ->
          let (transactionArguments, triggerArguments) = splitAt arity arguments'
           in pure (foldl renderApply
                (renderBasis name staticArguments transactionArguments)
                triggerArguments)
        _ -> pure (renderBasis name staticArguments arguments')
    M.EFfi moduleName name staticArguments
      | Set.member (moduleName, name) (foreignTagNames context) -> do
          arguments' <- mapM (renderExpr context locals) arguments
          pure (renderBasis name staticArguments arguments')
    M.EFfi moduleName name _ -> do
      arguments' <- mapM (renderExpr context locals) arguments
      case Map.lookup (moduleName, name) (foreignBindings context) of
        Nothing -> renderForeign context source moduleName name arguments'
        Just binding -> do
          let arity = length (NodeAddon.foreignBindingDomains binding)
              (foreignArguments, remainingArguments) = splitAt arity arguments'
          foreignCall <- renderForeign context source moduleName name foreignArguments
          pure (foldl renderApply foreignCall remainingArguments)
    _ -> do
      function' <- renderExpr context locals function
      arguments' <- mapM (renderExpr context locals) arguments
      pure (foldl renderApply function' arguments')

renderTagApplication
  :: JavaScriptContext
  -> [String]
  -> [M.StaticArg]
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> Generate String
renderTagApplication context locals staticArguments
    classes dynamicClass style dynamicStyle attributes descriptor child = do
  arguments <- sequence
    [ renderExpr context locals classes
    , renderDynamicOption context locals dynamicClass
    , renderExpr context locals style
    , renderDynamicOption context locals dynamicStyle
    , renderExpr context locals attributes
    , renderExpr context locals descriptor
    , renderExpr context locals child
    ]
  pure (renderBasis "tag" staticArguments arguments)

renderTagOpeningApplication
  :: JavaScriptContext
  -> [String]
  -> [M.StaticArg]
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> Generate String
renderTagOpeningApplication _ _ _
    classes dynamicClass style dynamicStyle attributes descriptor
  | Just name <- literalTagOpening classes dynamicClass style dynamicStyle attributes descriptor =
      renderPrimitive (PrimString HtmlString (ByteString.pack (map (fromIntegral . ord) ("<" <> name <> ">"))))
renderTagOpeningApplication context locals staticArguments
    classes dynamicClass style dynamicStyle attributes descriptor = do
  arguments <- sequence
    [ renderExpr context locals classes
    , renderDynamicOption context locals dynamicClass
    , renderExpr context locals style
    , renderDynamicOption context locals dynamicStyle
    , renderExpr context locals attributes
    , renderExpr context locals descriptor
    ]
  pure (renderBasis "__vr_tag_open" staticArguments arguments)

-- A fused opening tag with no attributes, dynamic bindings, or control name
-- is already a literal. Match only effect-free syntax and ordinary Basis
-- containers; foreign tags, input controls, and client islands keep the full
-- runtime path. In particular, do not discard an evaluated attribute or
-- descriptor argument just because its resulting record might be empty.
literalTagOpening :: M.Expr -> M.Expr -> M.Expr -> M.Expr -> M.Expr -> M.Expr -> Maybe String
literalTagOpening classes dynamicClass style dynamicStyle attributes descriptor
  | emptyString classes, absent dynamicClass, emptyString style, absent dynamicStyle
  , unit attributes
  , (function, arguments) <- collectApplications descriptor
  , all unit arguments
  , M.EFfi "Basis" name staticArguments <- locatedValue function
  , not (any isName staticArguments)
  , Set.member name ordinaryLiteralTags = Just name
  | otherwise = Nothing
  where
    emptyString expression = case locatedValue expression of
      M.EPrim (PrimString _ bytes) -> ByteString.null bytes
      _ -> False
    absent expression = case locatedValue expression of
      M.ENone _ -> True
      _ -> False
    unit expression = case locatedValue expression of
      M.ERecord [] -> True
      _ -> False
    isName M.StaticName {} = True
    isName _ = False

ordinaryLiteralTags :: Set.Set String
ordinaryLiteralTags = Set.fromList
  [ "body", "head", "title", "span", "div", "p", "strong", "em", "b", "i", "tt"
  , "sub", "sup", "h1", "h2", "h3", "h4", "h5", "h6", "li", "ol", "ul", "pre"
  , "section", "article", "nav", "aside", "footer", "header", "main", "meter"
  , "progress", "output", "keygen", "datalist", "details", "dialog", "menuitem"
  ]

renderForeign
  :: JavaScriptContext
  -> M.Expr
  -> String
  -> String
  -> [String]
  -> Generate String
renderForeign context source moduleName member arguments =
  case Map.lookup (moduleName, member) (foreignBindings context) of
    Nothing -> backendFailure source "javascript-ffi-signature"
      ("Server FFI has no generated native binding: " <> moduleName <> "." <> member)
    Just binding -> pure
      ("vr.foreign(" <> show (NodeAddon.foreignBindingId binding)
        <> ", " <> show (length (NodeAddon.foreignBindingDomains binding))
        <> ", " <> jsBool (NodeAddon.foreignBindingTransactional binding)
        <> ", [" <> intercalate ", " arguments <> "])")

renderDynamicOption :: JavaScriptContext -> [String] -> M.Expr -> Generate String
renderDynamicOption context locals option = case locatedValue option of
  M.ESome _ signal | Just identifier <- Map.lookup signal (clientDynamicIds context) -> do
    captures <- mapM captureAt
      (Map.findWithDefault [] signal (clientDynamicCaptureIndices context))
    pure ("({ tag: 1, payload: ({ __vrDynamic: " <> show identifier
      <> ", __vrCaptures: [" <> intercalate ", " captures <> "] }) })")
  _ -> renderExpr context locals option
  where
    captureAt index = case drop index locals of
      capture : _ -> pure capture
      [] -> backendFailure option "javascript-client-capture"
        ("Dynamic class/style signal refers to unavailable local " <> show index)

renderConstructor :: JavaScriptContext -> [String] -> M.PatCon -> Maybe M.Expr -> Generate String
renderConstructor context locals constructor payload = case constructor of
  M.PConFfi "Basis" "bool" "True" _ -> pure "true"
  M.PConFfi "Basis" "bool" "False" _ -> pure "false"
  M.PConFfi "Basis" "list" name _ -> tagged (if name == "Nil" then 0 else 1)
  M.PConVar identifier -> case Map.lookup identifier (constructorTags context) of
    Just tag -> tagged tag
    Nothing -> backendFailureAt payload "javascript-constructor" ("Unknown constructor #" <> show (M.unGlobalId identifier))
  M.PConFfi moduleName datatypeName name _ ->
    case Map.lookup (moduleName, datatypeName, name) (foreignConstructors context) of
      Nothing -> backendFailureAt payload "javascript-constructor"
        ("Unknown foreign constructor " <> moduleName <> "." <> datatypeName <> "." <> name)
      Just foreignConstructor -> do
        payload' <- maybe (pure []) (fmap pure . renderExpr context locals) payload
        pure ("vr.foreignConstructor(" <> show (Server.foreignConstructorId foreignConstructor)
          <> ", [" <> intercalate ", " payload' <> "])")
  where
    tagged :: Int -> Generate String
    tagged tag = do
      payload' <- maybe (pure "null") (renderExpr context locals) payload
      pure ("({ tag: " <> show tag <> ", payload: " <> payload' <> " })")

renderField
  :: JavaScriptContext
  -> [String]
  -> M.Expr
  -> (M.StaticArg, M.Expr, M.Type)
  -> Generate String
renderField context locals source (name, value, _) = do
  name' <- staticName source name
  value' <- case
    ( Map.lookup value (clientHandlerIds context)
    , Map.lookup value (clientDynamicIds context)
    , Map.lookup value (clientActiveIds context)
    ) of
    (Just identifier, _, _) -> capturedMarker "__vrHandler" identifier
      (Map.findWithDefault [] value (clientHandlerCaptureIndices context))
    (_, Just identifier, _) -> capturedMarker "__vrDynamic" identifier
      (Map.findWithDefault [] value (clientDynamicCaptureIndices context))
    (_, _, Just identifier) -> capturedMarker "__vrActive" identifier
      (Map.findWithDefault [] value (clientActiveCaptureIndices context))
    _ -> renderExpr context locals value
  pure (quoteString name' <> ": " <> value')
  where
    capturedMarker marker identifier indices = do
      captures <- mapM captureAt indices
      pure ("({ " <> marker <> ": " <> show identifier <> ", __vrCaptures: ["
        <> intercalate ", " captures <> "] })")
    captureAt index = case drop index locals of
      capture : _ -> pure capture
      [] -> backendFailure value "javascript-client-capture"
        ("Client handler refers to unavailable local " <> show index)

renderCase
  :: JavaScriptContext
  -> [String]
  -> M.Expr
  -> M.Expr
  -> [(M.Pattern, M.Expr)]
  -> Generate String
renderCase context locals source scrutinee branches = do
  scrutineeName <- freshName "scrutinee"
  scrutinee' <- renderExpr context locals scrutinee
  branchLines <- mapM (renderBranch context locals scrutineeName) branches
  if null branches
    then backendFailure source "javascript-empty-case" "A case expression has no branches"
    else pure
      ("(() => { const " <> scrutineeName <> " = vr.force(" <> scrutinee' <> "); "
        <> concat branchLines <> "return vr.matchFailure(); })()")

renderBranch
  :: JavaScriptContext
  -> [String]
  -> String
  -> (M.Pattern, M.Expr)
  -> Generate String
renderBranch context locals value (pattern', body) = do
  plan <- renderPattern context value pattern'
  let names = map fst (patternBindings plan)
      declarations = concat
        ["const " <> name <> " = " <> expression <> "; " | (name, expression) <- patternBindings plan]
  body' <- renderExpr context (reverse names <> locals) body
  pure
    ("if (" <> patternTest plan <> ") { " <> declarations <> "return " <> body' <> "; } ")

data PatternPlan = PatternPlan
  { patternTest :: !String
  , patternBindings :: ![(String, String)]
  }

renderPattern :: JavaScriptContext -> String -> M.Pattern -> Generate PatternPlan
renderPattern context value pattern' = case locatedValue pattern' of
  M.PVar _ _ -> do
    variable <- freshName "pattern"
    pure (PatternPlan "true" [(variable, value)])
  M.PPrim primitive -> do
    literal <- renderPrimitive primitive
    pure (PatternPlan ("vr.equal(" <> value <> ", " <> literal <> ")") [])
  M.PCon _ (M.PConFfi "Basis" "bool" name _) _ ->
    pure (PatternPlan (value <> " === " <> if name == "True" then "true" else "false") [])
  M.PCon _ (M.PConFfi "Basis" "list" name _) nested ->
    nestedTagged (if name == "Nil" then 0 else 1) nested
  M.PCon _ (M.PConVar identifier) nested -> case Map.lookup identifier (constructorTags context) of
    Just tag -> nestedTagged tag nested
    Nothing -> backendFailure pattern' "javascript-pattern-constructor"
      ("Unknown constructor #" <> show (M.unGlobalId identifier))
  M.PCon _ (M.PConFfi moduleName datatypeName name _) nested ->
    case Map.lookup (moduleName, datatypeName, name) (foreignConstructors context) of
      Nothing -> backendFailure pattern' "javascript-pattern-constructor"
        ("Unknown foreign constructor " <> moduleName <> "." <> datatypeName <> "." <> name)
      Just foreignConstructor -> nestedForeign foreignConstructor nested
  M.PRecord fields -> combinePatterns =<< mapM renderFieldPattern fields
  M.PNone _ -> pure (PatternPlan (value <> ".tag === 0") [])
  M.PSome _ nested -> do
    nested' <- renderPattern context (value <> ".payload") nested
    pure nested'
      { patternTest = "(" <> value <> ".tag === 1 && " <> patternTest nested' <> ")"
      }
  where
    nestedTagged :: Int -> Maybe M.Pattern -> Generate PatternPlan
    nestedTagged tag nested = case nested of
      Nothing -> pure (PatternPlan (value <> ".tag === " <> show tag) [])
      Just payload -> do
        nested' <- renderPattern context (value <> ".payload") payload
        pure nested'
          { patternTest =
              "(" <> value <> ".tag === " <> show tag <> " && " <> patternTest nested' <> ")"
          }
    nestedForeign constructor nested =
      let identifier = show (Server.foreignConstructorId constructor)
          matches = "vr.foreignConstructorMatches(" <> identifier <> ", " <> value <> ")"
       in case nested of
            Nothing -> pure (PatternPlan matches [])
            Just payload -> do
              nested' <- renderPattern context
                ("vr.foreignConstructorPayload(" <> identifier <> ", " <> value <> ")") payload
              pure nested'
                { patternTest = "(" <> matches <> " && " <> patternTest nested' <> ")" }
    renderFieldPattern (name, nested, _) =
      renderPattern context (value <> "[" <> quoteString name <> "]") nested

combinePatterns :: [PatternPlan] -> Generate PatternPlan
combinePatterns plans = pure PatternPlan
  { patternTest = case map patternTest plans of
      [] -> "true"
      tests -> "(" <> intercalate " && " tests <> ")"
  , patternBindings = concatMap patternBindings plans
  }

renderBasis :: String -> [M.StaticArg] -> [String] -> String
renderBasis name staticArguments arguments =
  "vr.basis(" <> quoteString name <> ", "
    <> renderStaticList (runtimeBasisArguments name staticArguments)
    <> ", [" <> intercalate ", " arguments <> "])"

-- The tag combinators consume seven/six value arguments; their static HTML
-- rows are only type-checking evidence.  Retain all arguments on descriptors
-- such as textbox and subform, whose static field names are runtime data.
runtimeBasisArguments :: String -> [M.StaticArg] -> [M.StaticArg]
runtimeBasisArguments name arguments
  | name == "tag" || name == "__vr_tag_open" = []
  | otherwise = arguments

renderApply :: String -> String -> String
renderApply function argument = "vr.app(" <> function <> ", " <> argument <> ")"

-- These are the same runtime operations used by Basis dispatch. Passing
-- operands as ordinary arguments keeps their evaluation and forcing order,
-- without allocating a Basis descriptor and argument arrays at each node.
renderGeneralBinary :: String -> String -> String -> String
renderGeneralBinary operator left right = case operator of
  "==" -> "vr.equal(" <> left <> ", " <> right <> ")"
  "<" -> call "binaryComparison" "lt"
  "<=" -> call "binaryComparison" "le"
  _ | operator `elem` ["+", "-", "*", "fdiv", "fmod", "powf"] -> call "binaryNumeric" operator
    | otherwise -> "vr.force(" <> renderBasis operator [] [left, right] <> ")"
  where
    call function name = "vr." <> function <> "(" <> quoteString name <> ", " <> left <> ", " <> right <> ")"

renderIntegerBinary :: String -> String -> String -> String
renderIntegerBinary operator left right = case operator of
  "+" -> arithmetic "+"
  "plus" -> arithmetic "+"
  "-" -> arithmetic "-"
  "minus" -> arithmetic "-"
  "*" -> arithmetic "*"
  "times" -> arithmetic "*"
  "==" -> comparison "==="
  "eq" -> comparison "==="
  "neq" -> comparison "!=="
  "<" -> comparison "<"
  "lt" -> comparison "<"
  "<=" -> comparison "<="
  "le" -> comparison "<="
  ">" -> comparison ">"
  "gt" -> comparison ">"
  ">=" -> comparison ">="
  "ge" -> comparison ">="
  _ -> "vr.integerBinary(" <> quoteString operator <> ", " <> left <> ", " <> right <> ")"
  where
    forced value = "vr.force(" <> value <> ")"
    arithmetic symbol =
      "vr.int64(" <> forced left <> " " <> symbol <> " " <> forced right <> ")"
    comparison symbol =
      "(" <> forced left <> " " <> symbol <> " " <> forced right <> ")"

renderPrimitive :: Primitive -> Generate String
renderPrimitive primitive = case primitive of
  PrimInt value -> pure (show value <> "n")
  PrimFloat value -> pure (show value)
  PrimChar value -> pure (show value)
  PrimString mode bytes -> do
    -- Decode immutable source literals once at module initialization, using
    -- the same runtime UTF-8 decoder (including malformed-byte behavior).
    -- HTML literals additionally share an immutable wrapper and the exact
    -- UTF-8 bytes written to the page. Ordinary string uses remain strings.
    let html = case mode of HtmlString -> True; _ -> False
    if ByteString.null bytes
      then pure (if html then "vr.safeHtml(\"\")" else "\"\"")
      else do
        state <- get
        identifier <- case Map.lookup bytes (stringLiterals state) of
          Just (identifier, usedAsString, usedAsHtml) -> do
            if (html && not usedAsHtml) || (not html && not usedAsString)
              then put state {stringLiterals = Map.insert bytes
                (identifier, usedAsString || not html, usedAsHtml || html) (stringLiterals state)}
              else pure ()
            pure identifier
          Nothing -> do
            let identifier = Map.size (stringLiterals state)
            put state {stringLiterals = Map.insert bytes (identifier, not html, html) (stringLiterals state)}
            pure identifier
        pure ((if html then pooledHtmlLiteralName else pooledLiteralName) identifier)

pooledLiteralName :: Int -> String
pooledLiteralName identifier = "vr_literal_" <> show identifier

pooledHtmlLiteralName :: Int -> String
pooledHtmlLiteralName identifier = "vr_html_literal_" <> show identifier

-- These writes either throw synchronously or return null. A comma expression
-- preserves left-to-right evaluation and exceptions without allocating a
-- continuation. General writes may return a Promise and keep vr.sequence.
immediateWrite :: M.Expr -> Bool
immediateWrite expression = case locatedValue expression of
  M.EWrite value -> case locatedValue value of
    M.EPrim (PrimString _ _) -> True
    _ | Just _ <- Server.integerHtmlArgument value -> True
    _ -> False
  _ -> False

renderType :: M.Type -> String
renderType typ = case locatedValue typ of
  M.TFun domain range -> object "function" [("domain", renderType domain), ("range", renderType range)]
  M.TRecord fields ->
    "{ tag: \"record\", fields: ["
      <> intercalate ", "
        ["[" <> quoteString name <> ", " <> renderType fieldType <> "]" | (name, fieldType) <- fields]
      <> "] }"
  M.TDatatype identifier -> object "datatype" [("id", show (M.unGlobalId identifier))]
  M.TFfi moduleName name ->
    "{ tag: \"ffi\", module: " <> quoteString moduleName <> ", name: " <> quoteString name <> " }"
  M.TOption element -> object "option" [("element", renderType element)]
  M.TList element -> object "list" [("element", renderType element)]
  M.TSource -> "{ tag: \"source\" }"
  M.TSignal element -> object "signal" [("element", renderType element)]

object :: String -> [(String, String)] -> String
object tag fields =
  "{ tag: " <> quoteString tag <> concat [", " <> name <> ": " <> value | (name, value) <- fields] <> " }"

renderStaticList :: [M.StaticArg] -> String
renderStaticList arguments = "[" <> intercalate ", " (map renderStatic arguments) <> "]"

renderStatic :: M.StaticArg -> String
renderStatic argument = case argument of
  M.StaticType typ -> object "type" [("value", renderType typ)]
  M.StaticName name -> object "name" [("value", quoteString name)]
  M.StaticRow fields ->
    object "row" [("fields", "[" <> intercalate ", "
      ["[" <> renderStatic name <> ", " <> renderStatic value <> "]" | (name, value) <- fields] <> "]")]
  M.StaticTuple elements -> object "tuple" [("elements", renderStaticList elements)]
  M.StaticFfi moduleName name arguments ->
    "{ tag: \"ffi\", module: " <> quoteString moduleName <> ", name: " <> quoteString name
      <> ", arguments: " <> renderStaticList arguments <> " }"
  M.StaticMap -> "{ tag: \"map\" }"
  M.StaticBound index -> object "bound" [("index", show index)]
  M.StaticLambda body -> object "lambda" [("body", renderStatic body)]
  M.StaticApply function value -> object "apply" [("function", renderStatic function), ("value", renderStatic value)]
  M.StaticProject tuple index -> object "project" [("tuple", renderStatic tuple), ("index", show index)]
  M.StaticConcat left right -> object "concat" [("left", renderStatic left), ("right", renderStatic right)]
  M.StaticUnit -> "{ tag: \"unit\" }"

renderQueryShape
  :: [(String, M.Type)]
  -> [(String, [(String, M.Type)])]
  -> M.Type
  -> String
renderQueryShape fields tables state =
  "{ fields: [" <> intercalate ", "
    ["[" <> quoteString name <> ", " <> renderType typ <> "]" | (name, typ) <- fields]
    <> "], tables: [" <> intercalate ", "
      ["[" <> quoteString table <> ", [" <> intercalate ", "
        ["[" <> quoteString name <> ", " <> renderType typ <> "]" | (name, typ) <- columns]
        <> "]]" | (table, columns) <- tables]
    <> "], state: " <> renderType state <> " }"

staticName :: Located value -> M.StaticArg -> Generate String
staticName _ (M.StaticName name) = pure name
staticName source _ = backendFailure source "javascript-static-name" "Record label is not statically known"

collectApplications :: M.Expr -> (M.Expr, [M.Expr])
collectApplications = go []
  where
    go arguments expression = case locatedValue expression of
      M.EApp function argument -> go (argument : arguments) function
      _ -> (expression, arguments)

basisTransactionArity :: String -> Maybe Int
basisTransactionArity name = lookup name
  [ ("channel", 0)
  , ("currentUrl", 0)
  , ("currentUrlHasPost", 0)
  , ("currentUrlHasQueryString", 0)
  , ("dml", 1)
  , ("fresh", 0)
  , ("new_channel", 0)
  , ("debug", 1)
  , ("getHeader", 1)
  , ("getenv", 1)
  , ("nextval", 1)
  , ("now", 0)
  , ("query", 3)
  , ("rand", 0)
  , ("self", 0)
  , ("recv", 1)
  , ("send", 2)
  , ("setval", 2)
  , ("setHeader", 2)
  , ("sleep", 1)
  , ("tryDml", 1)
  ]

htmlSafeExpression :: M.Expr -> Bool
htmlSafeExpression expression = case locatedValue expression of
  M.EPrim (PrimString HtmlString _) -> True
  M.EStrcat left right -> htmlSafeExpression left && htmlSafeExpression right
  _ -> False

collectConstructorTags :: [M.Decl] -> Map.Map M.GlobalId Int
collectConstructorTags declarations = Map.fromList
  [ (identifier, tag)
  | declaration <- declarations
  , M.DDatatype definitions <- [locatedValue declaration]
  , (_, _, constructors) <- definitions
  , (tag, (_, identifier, _)) <- zip [0 ..] constructors
  ]

collectGlobals :: [M.Decl] -> [M.GlobalId]
collectGlobals = concatMap collect
  where
    collect declaration = case locatedValue declaration of
      M.DVal _ identifier _ _ _ -> [identifier]
      M.DValRec bindings -> [identifier | (_, identifier, _, _, _) <- bindings]
      _ -> []

-- Ur/Web signs the values of environment variables whose names remain
-- statically visible in the server-side Mono program.  Keep the ordered-set
-- result here; the runtime intentionally consumes it in reverse order when it
-- constructs the compatibility payload.
collectXsrfEnvironment :: ProjectPlan -> [M.Decl] -> [String]
collectXsrfEnvironment plan declarations =
  Set.toAscList (foldMap declarationNames declarations)
  where
    clientOnly = Server.clientOnlyDefinitionIds plan declarations
    declarationNames declaration = case locatedValue declaration of
      M.DVal _ identifier _ expression _
        | not (Set.member identifier clientOnly) -> expressionNames expression
      M.DValRec bindings -> foldMap expressionNames
        [ expression
        | (_, identifier, _, expression, _) <- bindings
        , not (Set.member identifier clientOnly)
        ]
      M.DTable _ _ primary constraints -> expressionNames primary <> expressionNames constraints
      M.DView _ _ query -> expressionNames query
      M.DIndexDynamic table modes -> expressionNames table <> expressionNames modes
      M.DTask schedule body -> expressionNames schedule <> expressionNames body
      M.DPolicy policy -> case policy of
        M.PolicyClient expression -> expressionNames expression
        M.PolicyInsert expression -> expressionNames expression
        M.PolicyDelete expression -> expressionNames expression
        M.PolicyUpdate expression -> expressionNames expression
        M.PolicySequence expression -> expressionNames expression
      M.DPolicyRaw expression -> expressionNames expression
      _ -> Set.empty
    expressionNames expression = direct <> foldMap expressionNames (Server.serverExpressionChildren expression)
      where
        direct = case locatedValue expression of
          M.EFfiApp "Basis" "getenv" _ [(argument, _)] -> literalName argument
          M.EApp function argument -> case locatedValue function of
            M.EFfi "Basis" "getenv" _ -> literalName argument
            _ -> Set.empty
          _ -> Set.empty
        literalName argument = case locatedValue argument of
          M.EPrim (PrimString _ bytes) -> Set.singleton (bytesAsChars bytes)
          _ -> Set.empty

globalName :: M.GlobalId -> String
globalName identifier = "vr_g" <> show (M.unGlobalId identifier)

freshName :: String -> Generate String
freshName purpose = do
  state <- get
  let next = nextVariable state
  put state {nextVariable = next + 1}
  pure ("vr_" <> purpose <> "_" <> show next)

liftEither :: Either Diagnostic value -> Generate value
liftEither result = StateT $ \state -> case result of
  Left problem -> Left problem
  Right value -> Right (value, state)

exportKindName :: ExportKind -> String
exportKindName kind = case kind of
  Link _ -> "Link"
  Action _ -> "Action"
  Rpc _ -> "Rpc"
  Extern _ -> "Extern"

exportEffectName :: ExportKind -> String
exportEffectName kind = case kind of
  Link effect -> effectName effect
  Action effect -> effectName effect
  Rpc effect -> effectName effect
  Extern effect -> effectName effect

effectName :: Effect -> String
effectName effect = case effect of
  ReadOnly -> "read-only"
  ReadCookieWrite -> "read-cookie-write"
  ReadWrite -> "read-write"

failureModeName :: FailureMode -> String
failureModeName failure = case failure of
  FailureError -> "error"
  FailureNone -> "none"

sidednessName :: Sidedness -> String
sidednessName sidedness = case sidedness of
  PlacementPending -> "pending"
  ServerOnly -> "server"
  ServerAndPull -> "server-and-pull"
  ServerAndPullAndPush -> "server-and-pull-and-push"

databaseModeName :: DbMode -> String
databaseModeName mode = case mode of
  DbModePending -> "pending"
  NoDb -> "none"
  OneQuery -> "one-query"
  AnyDb -> "any"

javaScriptModeName :: M.JavaScriptMode -> String
javaScriptModeName mode = case mode of
  M.JavaScriptAttribute -> "attribute"
  M.JavaScriptScript -> "script"
  M.JavaScriptSource _ -> "source"

leadingSlash :: String -> String
leadingSlash value = case value of
  '/' : _ -> value
  _ -> '/' : value

hexBytes :: ByteString.ByteString -> String
hexBytes = concatMap byte . ByteString.unpack
  where
    byte value = let rendered = showHex value "" in if length rendered == 1 then '0' : rendered else rendered

bytesAsChars :: ByteString.ByteString -> String
bytesAsChars = map (toEnum . fromIntegral) . ByteString.unpack

quoteString :: String -> String
quoteString value = '"' : concatMap escape value <> "\""
  where
    escape character = case character of
      '"' -> "\\\""
      '\\' -> "\\\\"
      '\b' -> "\\b"
      '\f' -> "\\f"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      _
        | ord character < 0x20 -> "\\u" <> pad4 (showHex (ord character) "")
        | otherwise -> [character]
    pad4 rendered = replicate (4 - length rendered) '0' <> rendered

jsBool :: Bool -> String
jsBool True = "true"
jsBool False = "false"

backendFailure :: Located source -> String -> String -> Generate value
backendFailure source code message =
  StateT (const (Left (diagnostic BackendPhase code (locatedSpan source) message)))

backendFailureAt :: Maybe M.Expr -> String -> String -> Generate value
backendFailureAt source code message = case source of
  Just located -> backendFailure located code message
  Nothing -> StateT (const (Left (diagnostic BackendPhase code noSpan message)))
