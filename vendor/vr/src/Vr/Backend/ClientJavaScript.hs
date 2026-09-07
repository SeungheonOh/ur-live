{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Browser-side lowering shared by Vr's native and direct-JavaScript
-- servers.  Event handlers are compiled from Mono to ordinary JavaScript;
-- the server emits only a stable numeric reference in the corresponding HTML
-- attribute.  Each handler is emitted as a factory whose capture array is
-- supplied by the server-rendered page.
module Vr.Backend.ClientJavaScript
  ( ClientProgram (..)
  , compileClientProgram
  -- Playground adapter: expose the existing Mono expression emitter without
  -- changing its implementation or the native compiler checkout.
  , ClientContext (..)
  , renderExpr
  , finishCode
  , collectDefinitions
  , collectConstructorTags
  , reachableDefinitions
  , expressionDescendants
  , globalName
  ) where

import Control.Monad (forM)
import Control.Monad.State.Strict (StateT (..), evalStateT, get, put)
import qualified Data.ByteString as ByteString
import Data.Char (ord, toUpper)
import Data.Either (isRight)
import Data.List (intercalate, isSuffixOf, nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.String (IsString (..))
import Numeric (showHex)
import qualified Vr.Mono.Server as Server
import qualified Vr.Mono.Syntax as M
import Vr.Middle (Effect (..), FailureMode (..))
import Vr.Project
  ( FilterAction (..)
  , FilterKind (..)
  , FilterRule (..)
  , PatternKind (..)
  , ProjectDirective (..)
  , ProjectPlan (..)
  , projectFilterRules
  )
import Vr.Source
  ( Diagnostic
  , DiagnosticPhase (BackendPhase)
  , Located (..)
  , Primitive (..)
  , Span (..)
  , StringMode (HtmlString)
  , diagnostic
  )

data ClientProgram = ClientProgram
  { clientHandlers :: !(Map.Map M.Expr Int)
  , clientHandlerCaptures :: !(Map.Map M.Expr [Int])
  , clientHandlerCaptureTypes :: !(Map.Map M.Expr [M.Type])
  , clientDynamics :: !(Map.Map M.Expr Int)
  , clientDynamicCaptures :: !(Map.Map M.Expr [Int])
  , clientDynamicCaptureTypes :: !(Map.Map M.Expr [M.Type])
  , clientActives :: !(Map.Map M.Expr Int)
  , clientActiveCaptures :: !(Map.Map M.Expr [Int])
  , clientActiveCaptureTypes :: !(Map.Map M.Expr [M.Type])
  , clientClosures :: !(Map.Map M.Expr Int)
  , clientClosureCaptures :: !(Map.Map M.Expr [Int])
  , clientClosureCaptureTypes :: !(Map.Map M.Expr [M.Type])
  , clientHandlerAttributes :: ![(String, Int)]
  , clientScript :: !String
  }

data ClientForeignFunction = ClientForeignFunction
  { foreignJavaScriptName :: !String
  , foreignValueArity :: !Int
  , foreignTransactional :: !Bool
  }

-- These Basis values are runtime HTML/control descriptors.  Their static row
-- arguments exist for Ur's type checker; browser dispatch uses only the
-- selected constructor name.
clientHtmlTagNames :: Set.Set String
clientHtmlTagNames = Set.fromList (words
  "dyn active script head title link meta body br span div p strong em b i tt sub sup h1 h2 h3 h4 h5 h6 li ol ul hr pre section article nav aside footer header main meter progress output keygen datalist details dialog menuitem figure figcaption data mark rp rt ruby summary time wbr bdi a img form subform subforms entry hidden textbox password textarea checkbox email search url_ tel color number range date datetime datetime_local month week timeInput upload radio radioOption select option submit image label fieldset legend ctextbox cpassword cemail csearch curl ctel ccolor cnumber crange cdate cdatetime cdatetime_local cmonth cweek ctime button ccheckbox cradio cselect coption ctextarea tabl tr th td thead tbody tfoot dl dt dd")

data ClientContext = ClientContext
  { clientConstructors :: !(Map.Map M.GlobalId Int)
  , clientForeignConstructors :: !(Map.Map (String, String, String) Server.ForeignConstructor)
  , clientDefinitions :: !(Map.Map M.GlobalId M.Expr)
  , clientDatatypes :: !(Map.Map M.GlobalId [(String, Int, Maybe M.Type)])
  , contextHandlers :: !(Map.Map M.Expr Int)
  , contextHandlerCaptures :: !(Map.Map M.Expr [Int])
  , contextDynamics :: !(Map.Map M.Expr Int)
  , contextDynamicCaptures :: !(Map.Map M.Expr [Int])
  , contextActives :: !(Map.Map M.Expr Int)
  , contextActiveCaptures :: !(Map.Map M.Expr [Int])
  , clientForeignFunctions :: !(Map.Map (String, String) ClientForeignFunction)
  , clientForeignTags :: !(Set.Set Server.ForeignName)
  , clientUrlFilters :: ![FilterRule]
  , clientConfiguredTimeFormat :: !String
  }

type Generate = StateT Int (Either Diagnostic)

-- Client expressions are assembled bottom-up.  Using ordinary 'String'
-- concatenation here copies every nested expression once per ancestor (which
-- is particularly expensive for long generated expressions).  This
-- difference-list representation makes append constant-time while preserving
-- the exact text exposed by 'ClientProgram'.
newtype Code = Code { appendCode :: String -> String }

instance Semigroup Code where
  Code left <> Code right = Code (left . right)

instance Monoid Code where
  mempty = Code id

instance IsString Code where
  fromString value = Code (value <>)

codeText :: String -> Code
codeText value = Code (value <>)

finishCode :: Code -> String
finishCode output = appendCode output ""

joinCode :: Code -> [Code] -> Code
joinCode _ [] = mempty
joinCode separator (first : rest) =
  first <> foldMap (separator <>) rest

compileClientProgram :: ProjectPlan -> [String] -> M.File -> Either Diagnostic ClientProgram
compileClientProgram plan javascriptFiles file
  | null handlers && null dynamics && null actives && not clientRuntimeRequired =
      pure ClientProgram
        { clientHandlers = Map.empty
        , clientHandlerCaptures = Map.empty
        , clientHandlerCaptureTypes = Map.empty
        , clientDynamics = Map.empty
        , clientDynamicCaptures = Map.empty
        , clientDynamicCaptureTypes = Map.empty
        , clientActives = Map.empty
        , clientActiveCaptures = Map.empty
        , clientActiveCaptureTypes = Map.empty
        , clientClosures = Map.empty
        , clientClosureCaptures = Map.empty
        , clientClosureCaptureTypes = Map.empty
        , clientHandlerAttributes = []
        , clientScript = configuredScripts
        }
  | otherwise = do
      let declarations = M.fileDeclarations file
          handlerMap = Map.fromList (zip (map fst handlers) [0 ..])
          captureMap = Map.fromList [(handler, freeRelativeIndices handler) | (handler, _) <- handlers]
          dynamicMap = Map.fromList (zip dynamics [0 ..])
          dynamicCaptureMap = Map.fromList [(signal, freeRelativeIndices signal) | signal <- dynamics]
          activeMap = Map.fromList (zip actives [0 ..])
          activeCaptureMap = Map.fromList [(code, freeRelativeIndices code) | code <- actives]
          definitions = collectDefinitions declarations
          closureCandidates =
            [ nested
            | declaration <- declarations
            , expression <- declarationExpressions declaration
            , nested <- expressionDescendants expression
            , isClientFunctionCandidate nested
            ]
          closures = stableByExpr id (filter (clientClosureRenderable context definitions) closureCandidates)
          closureMap = Map.fromList (zip closures [0 ..])
          closureCaptureMap = Map.fromList
            [(closure, freeRelativeIndices closure) | closure <- closures]
          captureTargets = expressionTargets
            (Map.keys captureMap <> Map.keys dynamicCaptureMap
              <> Map.keys activeCaptureMap <> Map.keys closureCaptureMap)
          expressionEnvironments = clientExpressionEnvironments captureTargets file
          roots = Set.unions
            (map (expressionReferences . fst) handlers
              <> map expressionReferences dynamics
              <> map expressionReferences actives
              <> map expressionReferences closures)
          reachable = reachableDefinitions definitions roots
          context = ClientContext
            (collectConstructorTags declarations)
            (Map.fromList
              [ ( ( Server.foreignConstructorModule constructor
                  , Server.foreignConstructorDatatype constructor
                  , Server.foreignConstructorName constructor
                  )
                , constructor
                )
              | constructor <- Server.collectForeignConstructors file
              ])
            definitions
            (collectDatatypes declarations)
            handlerMap
            captureMap
            dynamicMap
            dynamicCaptureMap
            activeMap
            activeCaptureMap
            (foreignFunctions plan)
            (Server.foreignHtmlTagNames file)
            (filter ((== FilterUrl) . filterRuleKind) (projectFilterRules plan))
            (projectTimeFormat plan)
          attributes = nub
            [ (name, identifier)
            | declaration <- declarations
            , expression <- declarationExpressions declaration
            , nested <- expressionDescendants expression
            , M.ERecord fields <- [locatedValue nested]
            , (M.StaticName name, value, _) <- fields
            , Just identifier <- [Map.lookup value handlerMap]
            ]
      handlerCaptureTypeMap <- capturedTypeMap expressionEnvironments captureMap
      dynamicCaptureTypeMap <- capturedTypeMap expressionEnvironments dynamicCaptureMap
      activeCaptureTypeMap <- capturedTypeMap expressionEnvironments activeCaptureMap
      closureCaptureTypeMap <- capturedTypeMap expressionEnvironments closureCaptureMap
      output <- finishCode <$> evalStateT
        (renderProgram context reachable handlers dynamics actives closures) 0
      pure ClientProgram
        { clientHandlers = handlerMap
        , clientHandlerCaptures = captureMap
        , clientHandlerCaptureTypes = handlerCaptureTypeMap
        , clientDynamics = dynamicMap
        , clientDynamicCaptures = dynamicCaptureMap
        , clientDynamicCaptureTypes = dynamicCaptureTypeMap
        , clientActives = activeMap
        , clientActiveCaptures = activeCaptureMap
        , clientActiveCaptureTypes = activeCaptureTypeMap
        , clientClosures = closureMap
        , clientClosureCaptures = closureCaptureMap
        , clientClosureCaptureTypes = closureCaptureTypeMap
        , clientHandlerAttributes = attributes
        , clientScript = configuredScripts <> output
        }
  where
    handlers = stableByExpr fst
      [ handler
      | declaration <- M.fileDeclarations file
      , expression <- declarationExpressions declaration
      , handler <- eventHandlers expression
      ]
    dynamics = stableByExpr id
      [ signal
      | declaration <- M.fileDeclarations file
      , expression <- declarationExpressions declaration
      , signal <- dynamicSignals expression
      ]
    actives = stableByExpr id
      [ code
      | declaration <- M.fileDeclarations file
      , expression <- declarationExpressions declaration
      , code <- activeCodeBlocks expression
      ]
    clientRuntimeRequired = any declarationNeedsClientRuntime (M.fileDeclarations file)
    configuredScripts = projectScripts plan javascriptFiles

    projectTimeFormat project = case reverse
      [ projectDirectiveArgument directive
      | directive <- projectDirectives project
      , projectDirectiveName directive == "timeFormat"
      ] of
        format : _ -> format
        [] -> "%c"

    isClientFunctionCandidate expression = case locatedValue expression of
      M.EAbs {} -> not (null (freeRelativeIndices expression))
      M.EFfi moduleName _ _ -> moduleName /= "Basis"
      _ -> False

renderProgram
  :: ClientContext
  -> Set.Set M.GlobalId
  -> [(M.Expr, Bool)]
  -> [M.Expr]
  -> [M.Expr]
  -> [M.Expr]
  -> Generate Code
renderProgram context reachable handlers dynamics actives closures = do
  definitions <- fmap concat . forM (Map.toAscList (clientDefinitions context)) $ \(identifier, expression) ->
    if Set.member identifier reachable
      then do
        rendered <- isolated (renderExpr context [] expression)
        pure ["g[" <> codeText (show (M.unGlobalId identifier)) <> "]=" <> rendered <> ";"]
      else pure []
  renderedHandlers <- forM handlers $ \(handler, takesEvent) -> do
    rendered <- isolated (renderExpr context (capturedLocals handler) handler)
    pure $ "vr_captures=>" <> if takesEvent
      then "event=>rt.run(rt.app(" <> rendered <> ",rt.event(event)))"
      else "_event=>rt.run(" <> rendered <> ")"
  renderedDynamics <- forM dynamics $ \signal -> do
    rendered <- isolated (renderExpr context (capturedLocals signal) signal)
    pure ("vr_captures=>" <> rendered)
  renderedActives <- forM actives $ \code -> do
    rendered <- isolated (renderExpr context (capturedLocals code) code)
    pure ("vr_captures=>rt.run(" <> rendered <> ")")
  renderedClosures <- forM (zip [0 :: Int ..] closures) $ \(identifier, closure) -> do
    rendered <- isolated (renderExpr context (capturedLocals closure) closure)
    pure ("vr_captures=>Object.assign((" <> rendered
      <> "),{__vrClientClosure:{identifier:" <> codeText (show identifier)
      <> ",captures:vr_captures}})")
  pure ("<script>(()=>{\"use strict\";" <> codeText (clientRuntime context)
    <> "const g=Object.create(null);" <> mconcat definitions
    <> "globalThis.__vrHandlers=[" <> joinCode "," renderedHandlers <> "];"
    <> "globalThis.__vrDynamics=[" <> joinCode "," renderedDynamics <> "];"
    <> "globalThis.__vrActives=[" <> joinCode "," renderedActives <> "];"
    <> "globalThis.__vrClosures=[" <> joinCode "," renderedClosures <> "];"
    <> "if(document.readyState===\"loading\")document.addEventListener(\"DOMContentLoaded\",()=>rt.mount(),{once:true});else queueMicrotask(()=>rt.mount());"
    <> "})();</script>")

-- Generated names are lexically scoped inside each independent expression or
-- factory.  Resetting the counter avoids coupling output to unrelated roots
-- and exposes type-erased factories that are textually identical.
isolated :: Generate value -> Generate value
isolated generation = StateT $ \state ->
  fmap (\value -> (value, state)) (evalStateT generation 0)

capturedLocals :: M.Expr -> [Code]
capturedLocals expression =
  let captures = freeRelativeIndices expression
      captureSlots = Map.fromList (zip captures [0 :: Int ..])
   in case reverse captures of
        maximumIndex : _ ->
          [ maybe "undefined" (\slot -> "vr_captures[" <> codeText (show slot) <> "]")
              (Map.lookup index captureSlots)
          | index <- [0 .. maximumIndex]
          ]
        [] -> []

type ExpressionEnvironments = Map.Map Span ExpressionEnvironmentBucket

data ExpressionEnvironmentBucket
  = LinearEnvironments ![(M.Expr, [M.Type])]
  | IndexedEnvironments !(Map.Map M.Expr [M.Type])

capturedTypeMap
  :: ExpressionEnvironments
  -> Map.Map M.Expr [Int]
  -> Either Diagnostic (Map.Map M.Expr [M.Type])
capturedTypeMap environments = Map.traverseWithKey $ \expression indices ->
  case lookupExpressionEnvironment expression environments of
    Just environment -> mapM (captureAt expression environment) indices
    Nothing
      | null indices -> pure []
      | otherwise -> Left (diagnostic BackendPhase "client-capture-type"
          (locatedSpan expression)
          "The surrounding types of a captured client expression are unavailable")
  where
    captureAt expression environment index = case drop index environment of
      typ : _ -> pure typ
      [] -> Left (diagnostic BackendPhase "client-capture-type"
        (locatedSpan expression)
        ("Client expression captures unavailable local " <> show index))

lookupExpressionEnvironment :: M.Expr -> ExpressionEnvironments -> Maybe [M.Type]
lookupExpressionEnvironment expression environments = do
  bucket <- Map.lookup (locatedSpan expression) environments
  case bucket of
    LinearEnvironments entries -> lookup expression entries
    IndexedEnvironments entries -> Map.lookup expression entries

expressionTargets :: [M.Expr] -> Map.Map Span (Set.Set M.Expr)
expressionTargets = Map.fromListWith Set.union
  . map (\expression -> (locatedSpan expression, Set.singleton expression))

clientExpressionEnvironments
  :: Map.Map Span (Set.Set M.Expr)
  -> M.File
  -> ExpressionEnvironments
clientExpressionEnvironments targets file =
  Map.mapMaybeWithKey makeBucket (Map.fromListWith (++) entries)
  where
    entries =
      [ (locatedSpan nested, [(nested, environment)])
      | declaration <- M.fileDeclarations file
      , expression <- declarationExpressions declaration
      , (nested, environment) <- walk [] expression
      , Map.member (locatedSpan nested) targets
      ]
    makeBucket at values
      | length values > 8 =
          nonEmpty IndexedEnvironments
            (Map.restrictKeys (Map.fromList (reverse values)) desired)
      | otherwise = nonEmpty LinearEnvironments
          (filter (\(expression, _) -> Set.member expression desired) values)
      where
        desired = Map.findWithDefault Set.empty at targets
    nonEmpty constructor values
      | null values = Nothing
      | otherwise = Just (constructor values)
    walk environment expression = (expression, environment) : case locatedValue expression of
      M.EAbs _ domain _ body -> walk (domain : environment) body
      M.ELet _ typ value body -> walk environment value <> walk (typ : environment) body
      M.ECase scrutinee branches _ _ ->
        walk environment scrutinee
          <> concat
            [ walk (reverse (patternBindingTypes pattern') <> environment) body
            | (pattern', body) <- branches
            ]
      _ -> concatMap (walk environment) (expressionChildren expression)

clientClosureRenderable
  :: ClientContext
  -> Map.Map M.GlobalId M.Expr
  -> M.Expr
  -> Bool
clientClosureRenderable context definitions closure =
  renders (capturedLocals closure) closure
    && all (\identifier -> maybe False (renders []) (Map.lookup identifier definitions)) reachable
  where
    reachable = Set.toList
      (reachableDefinitions definitions (expressionReferences closure))
    renders locals expression =
      isRight (evalStateT (renderExpr context locals expression) 0)

patternBindingTypes :: M.Pattern -> [M.Type]
patternBindingTypes pattern' = case locatedValue pattern' of
  M.PVar _ typ -> [typ]
  M.PCon _ _ nested -> maybe [] patternBindingTypes nested
  M.PRecord fields -> concat [patternBindingTypes nested | (_, nested, _) <- fields]
  M.PSome _ nested -> patternBindingTypes nested
  _ -> []

renderExpr :: ClientContext -> [Code] -> M.Expr -> Generate Code
renderExpr context locals source = case locatedValue source of
  M.EPrim primitive -> pure (codeText (renderPrimitive primitive))
  M.ERel index -> case drop index locals of
    name : _ -> pure name
    [] -> failure source "client-local" ("Invalid client local index " <> show index)
  M.ENamed identifier -> pure (codeText (globalName identifier))
  M.ECon _ (M.PConFfi "Basis" "bool" name _) _ ->
    pure (if name == "True" then "true" else "false")
  M.ECon kind (M.PConFfi moduleName datatypeName name _) payload
    | moduleName /= "Basis" ->
        case Map.lookup (moduleName, datatypeName, name) (clientForeignConstructors context) of
          Nothing -> failure source "client-constructor"
            ("Unknown foreign constructor " <> moduleName <> "." <> datatypeName <> "." <> name)
          Just _ -> case (kind, payload) of
            (M.Option, Nothing) -> pure "null"
            (_, Nothing) -> pure (codeText (quote name))
            (_, Just value) -> do
              value' <- renderExpr context locals value
              pure ("({n:" <> codeText (quote name) <> ",v:" <> value' <> "})")
  M.ECon _ constructor payload -> do
    tag <- constructorTag context source constructor
    payload' <- maybe (pure "null") (renderExpr context locals) payload
    pure ("({tag:" <> codeText (show tag) <> ",payload:" <> payload' <> "})")
  M.ENone _ -> pure "({tag:0,payload:null})"
  M.ESome _ value -> do
    value' <- renderExpr context locals value
    pure ("({tag:1,payload:" <> value' <> "})")
  M.EFfi "Basis" name staticArguments ->
    pure ("rt.basis(" <> codeText (quote name) <> ","
      <> codeText (renderStaticList (runtimeStaticArguments name staticArguments)) <> ")")
  M.EFfi moduleName name _
    | Set.member (moduleName, name) (clientForeignTags context) ->
        pure ("rt.customTag(" <> codeText (quote name) <> ")")
  M.EFfi moduleName name _ -> case Map.lookup (moduleName, name) (clientForeignFunctions context) of
    Just custom -> pure ("rt.foreign(" <> codeText (quote (foreignJavaScriptName custom)) <> ","
      <> codeText (show (foreignValueArity custom)) <> ","
      <> codeText (jsBool (foreignTransactional custom)) <> ")")
    Nothing -> failure source "client-ffi"
      ("Browser lowering does not implement " <> moduleName <> "." <> name)
  M.EFfiApp "Basis" "urlifyForeign" staticArguments [(argument, _)] ->
    case staticArguments of
      M.StaticFfi moduleName typeName [] : _ ->
        let codecName = "urlify" <> capitalize typeName
         in case Map.lookup (moduleName, codecName) (clientForeignFunctions context) of
              Just custom -> do
                argument' <- renderExpr context locals argument
                pure ("rt.foreignCall(" <> codeText (quote (foreignJavaScriptName custom))
                  <> ",[" <> argument' <> "],false)")
              Nothing -> failure source "client-url-codec"
                ("Browser URL serialization for " <> moduleName <> "." <> typeName
                  <> " needs a jsFunc mapping for " <> moduleName <> "." <> codecName)
      _ -> failure source "client-url-codec"
        "Foreign browser URL serialization is missing its resolved codec type"
  M.EFfiApp "Basis" name staticArguments arguments -> do
    arguments' <- mapM (renderExpr context locals . fst) arguments
    pure ("rt.call(" <> codeText (quote name) <> ",[" <> joinCode "," arguments' <> "],"
      <> codeText (renderStaticList staticArguments) <> ")")
  M.EFfiApp moduleName name _ arguments
    | Set.member (moduleName, name) (clientForeignTags context) -> do
        arguments' <- mapM (renderExpr context locals . fst) arguments
        pure (foldl (\function argument -> "rt.app(" <> function <> "," <> argument <> ")")
          ("rt.customTag(" <> codeText (quote name) <> ")") arguments')
  M.EFfiApp moduleName name _ arguments -> case Map.lookup (moduleName, name) (clientForeignFunctions context) of
    Just custom -> do
      arguments' <- mapM (renderExpr context locals . fst) arguments
      pure ("rt.foreignCall(" <> codeText (quote (foreignJavaScriptName custom)) <> ",["
        <> joinCode "," arguments' <> "],"
        <> codeText (jsBool (foreignTransactional custom)) <> ")")
    Nothing -> failure source "client-ffi"
      ("Browser lowering does not implement " <> moduleName <> "." <> name)
  M.EApp {} -> renderClientApplication context locals source
  M.EAbs _ _ _ body -> do
    parameter <- fresh "argument"
    body' <- renderExpr context (parameter : locals) body
    pure (parameter <> "=>" <> body')
  M.EStaticApp function _ -> renderExpr context locals function
  M.EUnop operator value -> do
    value' <- renderExpr context locals value
    pure ("rt.unary(" <> codeText (quote operator) <> "," <> value' <> ")")
  M.EBinop _ operator left right -> do
    left' <- renderExpr context locals left
    right' <- renderExpr context locals right
    pure ("rt.binary(" <> codeText (quote operator) <> "," <> left' <> "," <> right' <> ")")
  M.ERecord fields -> do
    fields' <- mapM renderField fields
    pure ("({" <> joinCode "," fields' <> "})")
    where
      renderField (M.StaticName name, value, _) = do
        value' <- case
          ( Map.lookup value (contextHandlers context)
          , Map.lookup value (contextDynamics context)
          , Map.lookup value (contextActives context)
          ) of
            (Just identifier, _, _) -> capturedMarker "__vrHandler" identifier
              (Map.findWithDefault [] value (contextHandlerCaptures context))
            (_, Just identifier, _) -> capturedMarker "__vrDynamic" identifier
              (Map.findWithDefault [] value (contextDynamicCaptures context))
            (_, _, Just identifier) -> capturedMarker "__vrActive" identifier
              (Map.findWithDefault [] value (contextActiveCaptures context))
            _ -> renderExpr context locals value
        pure (codeText (quote name) <> ":" <> value')
      renderField _ = failure source "client-record" "A client record retained a dynamic field name"
      capturedMarker marker identifier indices = do
        captures <- mapM captureAt indices
        pure ("({" <> codeText marker <> ":" <> codeText (show identifier) <> ",__vrCaptures:["
          <> joinCode "," captures <> "]})")
      captureAt index = case drop index locals of
        capture : _ -> pure capture
        [] -> failure source "client-capture"
          ("Client expression refers to unavailable local " <> show index)
  M.EField record (M.StaticName name) -> do
    record' <- renderExpr context locals record
    pure ("rt.force(" <> record' <> ")[" <> codeText (quote name) <> "]")
  M.EField _ _ -> failure source "client-record" "A client projection retained a dynamic field name"
  M.ERecordConcat left right -> do
    left' <- renderExpr context locals left
    right' <- renderExpr context locals right
    pure ("({...rt.force(" <> left' <> "),...rt.force(" <> right' <> ")})")
  M.ERecordCut record fields -> do
    record' <- renderExpr context locals record
    names <- mapM (staticName source) fields
    pure ("rt.cut(" <> record' <> ",["
      <> joinCode "," (map (codeText . quote) names) <> "])")
  M.ECase scrutinee branches _ _ -> renderCase context locals source scrutinee branches
  M.EStrcat left right -> do
    left' <- renderExpr context locals left
    right' <- renderExpr context locals right
    pure ("rt.concat(" <> left' <> "," <> right' <> ")")
  M.EError message _ -> do
    message' <- renderExpr context locals message
    pure ("rt.fail(" <> message' <> ")")
  M.EReturnBlob {} -> unsupported "blob response"
  M.ERedirect value _ -> do
    value' <- renderExpr context locals value
    pure ("rt.redirect(" <> value' <> ")")
  M.EWrite value -> do
    value' <- renderExpr context locals value
    pure ("rt.write(" <> value' <> ")")
  M.ESeq first second -> do
    first' <- renderExpr context locals first
    second' <- renderExpr context locals second
    pure ("rt.sequence(" <> first' <> ",()=>" <> second' <> ")")
  M.ELet _ _ value body -> do
    variable <- fresh "local"
    value' <- renderExpr context locals value
    body' <- renderExpr context (variable : locals) body
    pure ("rt.letValue(" <> value' <> "," <> variable <> "=>" <> body' <> ")")
  M.EClosure identifier captures -> do
    captures' <- mapM (renderExpr context locals) captures
    pure ("rt.closure(" <> codeText (globalName identifier) <> ",["
      <> joinCode "," captures' <> "])")
  M.EQuery {} -> unsupported "database query"
  M.EDml {} -> unsupported "database command"
  M.ENextval {} -> unsupported "database sequence"
  M.ESetval {} -> unsupported "database sequence"
  M.EUnurlify value _ optional -> do
    value' <- renderExpr context locals value
    pure (if optional then "({tag:1,payload:" <> value' <> "})" else value')
  M.EJavaScript _ value -> renderExpr context locals value
  M.ESignalReturn value -> do
    value' <- renderExpr context locals value
    pure ("rt.signalReturn(" <> value' <> ")")
  M.ESignalBind signal continuation -> do
    signal' <- renderExpr context locals signal
    continuation' <- renderExpr context locals continuation
    pure ("rt.signalBind(" <> signal' <> "," <> continuation' <> ")")
  M.ESignalSource value -> do
    value' <- renderExpr context locals value
    pure ("rt.signalSource(" <> value' <> ")")
  M.EServerCall call typ effect failureMode -> do
    call' <- renderExpr context locals call
    pure ("rt.serverCall(" <> call' <> "," <> codeText (renderType typ) <> ","
      <> codeText (quote (case failureMode of FailureNone -> "none"; FailureError -> "error")) <> ","
      <> codeText (jsBool (effect == ReadCookieWrite)) <> ")")
  M.ERecv channel typ -> do
    channel' <- renderExpr context locals channel
    pure ("rt.channelRecv(" <> channel' <> "," <> codeText (renderType typ) <> ")")
  M.ESleep duration -> do
    duration' <- renderExpr context locals duration
    pure ("rt.sleep(" <> duration' <> ")")
  M.ESpawn action -> do
    action' <- renderExpr context locals action
    pure ("rt.spawn(" <> action' <> ")")
  M.ESqlCache {} -> unsupported "server SQL cache"
  M.ESqlCacheFlush {} -> unsupported "server SQL cache invalidation"
  where
    -- Static row/type operands select and type-check an HTML constructor, but
    -- the browser runtime dispatches the already selected constructor by name
    -- and never inspects those operands.  Erasing them avoids shipping the
    -- complete resolved HTML schema at every tag occurrence.
    runtimeStaticArguments name arguments
      | name `elem` ["tag", "__vr_tag_open"] = []
      | Set.member name clientHtmlTagNames = []
      | Set.member ("Basis", name) (clientForeignTags context) = []
      | otherwise = arguments
    unsupported feature = failure source "client-expression"
      ("Browser lowering does not yet implement " <> feature)

renderClientApplication :: ClientContext -> [Code] -> M.Expr -> Generate Code
renderClientApplication context locals source = do
  let (function, arguments) = collectApplications source
  function' <- renderExpr context locals function
  arguments' <- case (locatedValue function, arguments) of
    (M.EFfi "Basis" "tag" _, [classes, dynamicClass, style, dynamicStyle, attributes, descriptor, child]) ->
      sequence
        [ renderExpr context locals classes
        , renderDynamicOption context locals dynamicClass
        , renderExpr context locals style
        , renderDynamicOption context locals dynamicStyle
        , renderExpr context locals attributes
        , renderExpr context locals descriptor
        , renderExpr context locals child
        ]
    (M.EFfi "Basis" "__vr_tag_open" _, [classes, dynamicClass, style, dynamicStyle, attributes, descriptor]) ->
      sequence
        [ renderExpr context locals classes
        , renderDynamicOption context locals dynamicClass
        , renderExpr context locals style
        , renderDynamicOption context locals dynamicStyle
        , renderExpr context locals attributes
        , renderExpr context locals descriptor
        ]
    _ -> mapM (renderExpr context locals) arguments
  pure (mconcat (replicate (length arguments') "rt.app(") <> function'
    <> foldMap (\argumentCode -> "," <> argumentCode <> ")") arguments')

renderDynamicOption :: ClientContext -> [Code] -> M.Expr -> Generate Code
renderDynamicOption context locals option = case locatedValue option of
  M.ESome _ signal | Just identifier <- Map.lookup signal (contextDynamics context) -> do
    captures <- mapM captureAt (Map.findWithDefault [] signal (contextDynamicCaptures context))
    pure ("({tag:1,payload:{__vrDynamic:" <> codeText (show identifier) <> ",__vrCaptures:["
      <> joinCode "," captures <> "]}})")
  _ -> renderExpr context locals option
  where
    captureAt index = case drop index locals of
      capture : _ -> pure capture
      [] -> failure option "client-capture"
        ("Dynamic class/style signal refers to unavailable local " <> show index)

renderCase
  :: ClientContext
  -> [Code]
  -> M.Expr
  -> M.Expr
  -> [(M.Pattern, M.Expr)]
  -> Generate Code
renderCase context locals _source scrutinee branches = do
  scrutineeName <- fresh "scrutinee"
  scrutinee' <- renderExpr context locals scrutinee
  branchLines <- mapM (renderBranch scrutineeName) branches
  pure ("(()=>{const " <> scrutineeName <> "=rt.force(" <> scrutinee' <> ");"
    <> mconcat branchLines <> "return rt.matchFailure();})()")
  where
    renderBranch value (pattern', body) = do
      plan <- renderPattern context value pattern'
      body' <- renderExpr context (reverse (map fst (patternBindings plan)) <> locals) body
      let bindings = mconcat
            ["const " <> name <> "=" <> expression <> ";" | (name, expression) <- patternBindings plan]
      pure ("if(" <> patternTest plan <> "){" <> bindings <> "return " <> body' <> ";}")

data PatternPlan = PatternPlan
  { patternTest :: !Code
  , patternBindings :: ![(Code, Code)]
  }

renderPattern :: ClientContext -> Code -> M.Pattern -> Generate PatternPlan
renderPattern context value pattern' = case locatedValue pattern' of
  M.PVar _ _ -> do
    name <- fresh "pattern"
    pure (PatternPlan "true" [(name, value)])
  M.PPrim primitive -> pure
    (PatternPlan ("rt.equal(" <> value <> "," <> codeText (renderPrimitive primitive) <> ")") [])
  M.PCon _ (M.PConFfi "Basis" "bool" name _) _ ->
    pure (PatternPlan (value <> "===" <> if name == "True" then "true" else "false") [])
  M.PCon kind (M.PConFfi moduleName datatypeName name _) nested
    | moduleName /= "Basis" ->
        case Map.lookup (moduleName, datatypeName, name) (clientForeignConstructors context) of
          Nothing -> failure pattern' "client-constructor"
            ("Unknown foreign constructor " <> moduleName <> "." <> datatypeName <> "." <> name)
          Just _ -> foreignPattern kind name nested
  M.PCon _ constructor nested -> tagged nested =<< constructorTag context pattern' constructor
  M.PRecord fields -> combinePatterns =<< mapM
    (\(name, nested, _) -> renderPattern context
      (value <> "[" <> codeText (quote name) <> "]") nested) fields
  M.PNone _ -> pure (PatternPlan (value <> ".tag===0") [])
  M.PSome _ nested -> do
    nested' <- renderPattern context (value <> ".payload") nested
    pure nested' {patternTest = "(" <> value <> ".tag===1&&" <> patternTest nested' <> ")"}
  where
    tagged nested tag = case nested of
      Nothing -> pure (PatternPlan (value <> ".tag===" <> codeText (show tag)) [])
      Just payload -> do
        nested' <- renderPattern context (value <> ".payload") payload
        pure nested'
          {patternTest = "(" <> value <> ".tag===" <> codeText (show tag)
            <> "&&" <> patternTest nested' <> ")"}
    foreignPattern kind name nested =
      let outer = case (kind, nested) of
            (M.Option, Nothing) -> value <> "===null"
            (M.Option, Just _) -> value <> "!==null"
            (_, Nothing) -> value <> "===" <> codeText (quote name)
            (_, Just _) -> value <> "!==null&&" <> value <> ".n===" <> codeText (quote name)
       in case nested of
            Nothing -> pure (PatternPlan outer [])
            Just payload -> do
              nested' <- renderPattern context (value <> ".v") payload
              pure nested' {patternTest = "(" <> outer <> "&&" <> patternTest nested' <> ")"}

combinePatterns :: [PatternPlan] -> Generate PatternPlan
combinePatterns plans = pure PatternPlan
  { patternTest = case map patternTest plans of
      [] -> "true"
      tests -> "(" <> joinCode "&&" tests <> ")"
  , patternBindings = concatMap patternBindings plans
  }

constructorTag :: ClientContext -> Located value -> M.PatCon -> Generate Int
constructorTag context source constructor = case constructor of
  M.PConFfi "Basis" "bool" "False" _ -> pure 0
  M.PConFfi "Basis" "bool" "True" _ -> pure 1
  M.PConFfi "Basis" "list" "Nil" _ -> pure 0
  M.PConFfi "Basis" "list" "Cons" _ -> pure 1
  M.PConFfi "Basis" "mouseButton" "Left" _ -> pure 0
  M.PConFfi "Basis" "mouseButton" "Right" _ -> pure 1
  M.PConFfi "Basis" "mouseButton" "Middle" _ -> pure 2
  M.PConVar identifier -> case Map.lookup identifier (clientConstructors context) of
    Just tag -> pure tag
    Nothing -> failure source "client-constructor" ("Unknown client constructor #" <> show (M.unGlobalId identifier))
  M.PConFfi moduleName datatypeName name _ -> failure source "client-constructor"
    ("Browser lowering does not implement " <> moduleName <> "." <> datatypeName <> "." <> name)

clientRuntime :: ClientContext -> String
clientRuntime context = concat
  [ "const rt=(dt=>{"
  , "const urlRules=" <> renderUrlFilters context
      <> ";const configuredTimeFormat=" <> quote (clientConfiguredTimeFormat context) <> ";"
  , "const td=new TextDecoder();const bytes=h=>td.decode(Uint8Array.from(h.match(/../g)||[],x=>parseInt(x,16)));"
  , "const force=x=>x;const app=(f,x)=>{if(typeof f!==\"function\")throw new TypeError(\"Attempted to apply a non-function Ur value\");return f(x)};"
  , "const tx=f=>{f.__vrTransaction=true;return f};"
  , "const handlerLists={error:[],fail:[],connectFail:[],disconnect:[],serverError:[]};const runHandlers=(kind,arg,acceptsArgument=true)=>{const handlers=handlerLists[kind];if(handlers.length===0){globalThis.alert?.((kind===\"connectFail\"?\"RPC failure\":kind)+\": \"+text(arg));return}for(const handler of handlers)Promise.resolve().then(async()=>{let value=acceptsArgument?app(handler,arg):handler;if(typeof value===\"function\")value=value(null);await value}).catch(()=>{})};const registerHandler=(kind,handler)=>tx(()=>{handlerLists[kind].unshift(handler);return null});"
  , "const run=async x=>{try{if(typeof x===\"function\")x=x(null);return await x}catch(e){if(!e?.__vrReportedError)runHandlers(\"fail\",e?.message??String(e));setTimeout(()=>{throw e});}};"
  , "const isHtml=x=>!!(x&&typeof x===\"object\"&&x.__vrHtml===true);const text=x=>x==null?\"\":isHtml(x)?x.value:typeof x===\"bigint\"?x.toString():String(x);const html=x=>({__vrHtml:true,value:text(x)});const escape=x=>text(x).replaceAll(\"&\",\"&amp;\").replaceAll(\"<\",\"&lt;\").replaceAll(\">\",\"&gt;\").replaceAll('\\\"',\"&quot;\").replaceAll(\"'\",\"&#39;\");const htmlify=x=>[...text(x)].map(c=>{const n=c.codePointAt(0);return n>=32&&n<=126?c===\"&\"?\"&amp;\":c===\"<\"?\"&lt;\":c:\"&#\"+n+\";\"}).join(\"\");const attrify=x=>text(x).replaceAll(\"&\",\"&amp;\").replaceAll('\\\"',\"&quot;\");const css=(kind,x)=>{x=text(x);if(kind===\"property\"){if(x===\"\")throw new Error(\"Empty CSS property\");if(!/^[a-z_]/.test(x))throw new Error(\"Bad initial character in CSS property\");if(!/^[a-z_][a-z0-9_\\-]*$/.test(x))throw new Error(\"Disallowed character in CSS property\")}else if(!(kind===\"atom\"?/^[A-Za-z0-9+.#%\\-]*$/:/^[A-Za-z0-9:/._+%?&=#\\-]*$/).test(x))throw new Error(\"Disallowed character in CSS \"+kind);return x};"
  , "const checkUrl=x=>{x=text(x);for(const rule of urlRules)if(rule.prefix?x.startsWith(rule.pattern):x===rule.pattern)return rule.allow?option(x):option(null);return option(null)};const bless=x=>{const checked=checkUrl(x);if(checked.tag===0)throw new Error(\"Disallowed URL: \"+text(x));return checked.payload};"
  , "const equal=(a,b)=>a===b||!!(a&&b&&typeof a===\"object\"&&typeof b===\"object\"&&Object.keys(a).length===Object.keys(b).length&&Object.keys(a).every(k=>equal(a[k],b[k])));"
  , "const binary=(n,a,b)=>{switch(n){case\"=\":case\"==\":case\"eq\":return equal(a,b);case\"!strcmp\":return text(a)===text(b);case\"strcmp\":return BigInt(text(a)<text(b)?-1:text(a)>text(b)?1:0);case\"<>\":case\"!=\":case\"neq\":return!equal(a,b);case\"<\":case\"lt\":return a<b;case\"<=\":case\"le\":return a<=b;case\">\":case\"gt\":return a>b;case\">=\":case\"ge\":return a>=b;case\"+\":case\"plus\":return a+b;case\"-\":case\"minus\":return a-b;case\"*\":case\"times\":return a*b;case\"/\":case\"div\":return a/b;case\"%\":case\"mod\":return a%b;case\"powl\":case\"powf\":case\"pow\":return a**b;case\"&&\":case\"and\":return a&&b;case\"||\":case\"or\":return a||b;default:throw new Error(\"Unknown Ur operator \"+n)}};"
  , "const unary=(n,x)=>n===\"-\"?-x:n===\"not\"?!x:x;"
  , "const foreignTarget=n=>{const path=String(n).split(\".\");let owner=globalThis,value=owner;for(const part of path){owner=value;value=value?.[part]}if(typeof value!==\"function\")throw new Error(\"Missing JavaScript FFI function \"+n);return[owner,value]};const rawForeignCall=(n,a)=>{const[owner,value]=foreignTarget(n);return value.apply(owner,a)};const foreignCall=(n,a,transactional=false)=>transactional?tx(()=>rawForeignCall(n,a)):rawForeignCall(n,a);const foreign=(n,arity,transactional=false)=>{const collect=a=>x=>{const next=[...a,x];return next.length>=arity?foreignCall(n,next,transactional):collect(next)};return arity===0?foreignCall(n,[],transactional):collect([])};"
  , "const option=x=>x===null||x===undefined?{tag:0,payload:null}:{tag:1,payload:x};const codepoints=x=>[...text(x)];const integer=x=>{const s=text(x),m=s.match(/^[\\t\\n\\v\\f\\r ]*([+-]?[0-9]+)$/);if(!m)return null;let n;try{n=BigInt(m[1])}catch{return null}const lo=-(1n<<63n),hi=(1n<<63n)-1n;return n<lo?lo:n>hi?hi:n};const floating=x=>{const s=text(x);if(!/^[\\t\\n\\v\\f\\r ]*[+-]?(?:(?:[0-9]+(?:\\.[0-9]*)?|\\.[0-9]+)(?:[eE][+-]?[0-9]+)?|inf(?:inity)?|nan)$/i.test(s))return null;return Number(s)};const character=x=>{const c=codepoints(x);return c.length===1?c[0].codePointAt(0):null};"
  , "const micros=t=>BigInt(t?.seconds??0)*1000000n+BigInt(t?.microseconds??0);const fromMicros=n=>{n=BigInt(n);let seconds=n/1000000n,microseconds=n%1000000n;if(microseconds<0){seconds--;microseconds+=1000000n}return{seconds,microseconds}};const pad=(x,n=2,fill=\"0\")=>String(x).padStart(n,fill);const timeParts=t=>{const u=micros(t);return new Date(Number(u>=0n?u/1000n:(u-999n)/1000n))};const dayOfYear=d=>Math.trunc((Date.UTC(d.getFullYear(),d.getMonth(),d.getDate())-Date.UTC(d.getFullYear(),0,1))/86400000)+1;const weekMonday=d=>Math.trunc((dayOfYear(d)+7-(d.getDay()||7))/7);const weekSunday=d=>Math.trunc((dayOfYear(d)+6-d.getDay())/7);const isoNumber=d=>{const w=weekMonday(d),janDay=new Date(d.getFullYear(),0,1).getDay();let n=w+(janDay>4||janDay<=1?0:1);if(n===53&&new Date(d.getFullYear(),11,31).getDay()<4)n=1;else if(n===0)n=isoNumber(new Date(d.getFullYear()-1,11,31));return n};const isoYear=d=>{let y=d.getFullYear(),v=isoNumber(d),w=weekMonday(d);if(w>v)y++;else if(w===0&&v>=52)y--;return y};const zoneOffset=d=>{const o=d.getTimezoneOffset(),a=Math.abs(o);return(o>0?\"-\":\"+\")+pad(Math.trunc(a/60))+pad(a%60)};const zoneName=d=>{const value=d.toString().match(/\\(([^)]+)\\)$/)?.[1]??\"\",short=value.replace(/[a-z ]/g,\"\");return short.length>0&&short.length<=4?short:zoneOffset(d)};const timeFormat=(format,t)=>{const d=timeParts(t),days=[\"Sun\",\"Mon\",\"Tue\",\"Wed\",\"Thu\",\"Fri\",\"Sat\"],longDays=[\"Sunday\",\"Monday\",\"Tuesday\",\"Wednesday\",\"Thursday\",\"Friday\",\"Saturday\"],months=[\"Jan\",\"Feb\",\"Mar\",\"Apr\",\"May\",\"Jun\",\"Jul\",\"Aug\",\"Sep\",\"Oct\",\"Nov\",\"Dec\"],longMonths=[\"January\",\"February\",\"March\",\"April\",\"May\",\"June\",\"July\",\"August\",\"September\",\"October\",\"November\",\"December\"],aggregates={c:\"%a %d %b %Y %T %Z\",D:\"%m/%d/%y\",F:\"%Y-%m-%d\",h:\"%b\",n:\"\\n\",r:\"%I:%M:%S %p\",R:\"%H:%M\",t:\"\\t\",T:\"%H:%M:%S\",x:\"%d/%m/%y\",X:\"%T\"};format=text(format);while(/%[cDFhnrRtTxX]/.test(format))format=format.replace(/%([cDFhnrRtTxX])/g,(_,code)=>aggregates[code]);return format.replace(/%([aAbBCdegGHIjklmMpPsSuUVwWyYzZ%])/g,(_,code)=>({\"%\":\"%\",a:days[d.getDay()],A:longDays[d.getDay()],b:months[d.getMonth()],B:longMonths[d.getMonth()],C:pad(Math.trunc(d.getFullYear()/100)),d:pad(d.getDate()),e:pad(d.getDate(),2,\" \"),g:pad(isoYear(d)%100),G:String(isoYear(d)),H:pad(d.getHours()),I:pad(d.getHours()%12||12),j:pad(dayOfYear(d),3),k:pad(d.getHours(),2,\" \"),l:pad(d.getHours()%12||12,2,\" \"),m:pad(d.getMonth()+1),M:pad(d.getMinutes()),p:d.getHours()>=12?\"PM\":\"AM\",P:d.getHours()>=12?\"pm\":\"am\",s:String(Math.trunc(d.getTime()/1000)),S:pad(d.getSeconds()),u:String(d.getDay()||7),U:pad(weekSunday(d)),V:pad(isoNumber(d)),w:String(d.getDay()),W:pad(weekMonday(d)),y:pad(d.getFullYear()%100),Y:String(d.getFullYear()),z:zoneOffset(d),Z:zoneName(d)})[code]??code)};"
  , "let nextFreshId=0,currentBrowserEvent=null;const fresh=()=>\"uw\"+(--nextFreshId);const originalEvent=e=>e?.__vrEvent??currentBrowserEvent??e;const globalEvent=(name,handler)=>tx(()=>{document.addEventListener(name,value=>run(app(handler,event(value))));return null});const basisArities={stringToTime:1,stringToTime_error:1,htmlifyBool:1,htmlifyFloat:1,htmlifyInt:1,htmlifyString:1,htmlifyTime:1,htmlifySpecialChar:1,stringToFloat:1,stringToInt:1,stringToChar:1,stringToBool:1,stringToFloat_error:1,stringToInt_error:1,stringToChar_error:1,stringToBool_error:1,urlifyInt:1,urlifyFloat:1,urlifyTime:1,urlifyString:1,urlifyChar:1,urlifyBool:1,intToString:1,floatToString:1,charToString:1,boolToString:1,attrifyString:1,attrifyInt:1,attrifyFloat:1,attrifyBool:1,str1:1,strsub:2,strsubUtf8:2,strsuffix:2,strsuffixUtf8:2,strlen:1,strlenUtf8:1,strindex:2,strsindex:2,strchr:2,substring:3,strcspn:2,strlenGe:2,islower:1,isupper:1,isalpha:1,isdigit:1,isalnum:1,isblank:1,isspace:1,isxdigit:1,isprint:1,tolower:1,toupper:1,ord:1,anchorUrl:1,eq_time:2,lt_time:2,le_time:2,floatFromInt:1,ceil:1,trunc:1,round:1,floor:1,pow:2,sqrt:1,sin:1,cos:1,log:1,exp:1,asin:1,acos:1,atan:1,atan2:2,abs:1,timeToString:1,timef:2,toSeconds:1,addSeconds:2,diffInSeconds:2,toMilliseconds:1,fromMilliseconds:1,diffInMilliseconds:2,fromDatetime:6,datetimeYear:1,datetimeMonth:1,datetimeDay:1,datetimeHour:1,datetimeMinute:1,datetimeSecond:1,datetimeDayOfWeek:1,chr:1};const curryCall=(name,staticArguments,arity=basisArities[name]??1,arguments_=[])=>value=>{const next=[...arguments_,value];return next.length>=arity?call(name,next,staticArguments):curryCall(name,staticArguments,arity,next)};"
  , "const rawSource=x=>({value:x,listeners:new Set()});const source=x=>{const s=rawSource(x);s.clientId=globalThis.__vrSources.length;globalThis.__vrSources.push(s);return s};const publish=(s,x)=>{s.value=x;for(const f of [...s.listeners])f(x)};const set=(s,x)=>tx(()=>{publish(s,x);return null});const get=s=>tx(()=>s.value);"
  , "globalThis.__vrSources??=[];for(const[clientId,value]of(globalThis.__vrSourceInitials||[]).entries()){globalThis.__vrSources[clientId]??={};globalThis.__vrSources[clientId].value=value}const prepareSources=()=>{for(const[clientId,sourceValue]of globalThis.__vrSources.entries())if(sourceValue){sourceValue.listeners??=new Set();sourceValue.clientId=clientId}};prepareSources();const decodeCaptures=value=>value?(0,Function)(\"return (\"+value+\")\")():[];const captureValues=node=>node.dataset.vrCaptures?decodeCaptures(node.dataset.vrCaptures):(node.dataset.vrSourceCaptures||\"\").split(\",\").filter(Boolean).map(id=>globalThis.__vrSources[Number(id)]);const nodes=(root,selector)=>[...(root.matches?.(selector)?[root]:[]),...root.querySelectorAll(selector)];"
  , "const mountControl=node=>{if(node.dataset.vrMounted)return;node.dataset.vrMounted=\"1\";const s=globalThis.__vrSources[Number(node.dataset.vrControlSource)];if(!s)return;const kind=node.dataset.vrControlKind;const draw=v=>{if(kind===\"bool\")node.checked=!!v;else if(kind===\"radio\")node.checked=v?.tag===1&&text(v.payload)===node.value;else if(kind===\"option-float\")node.value=v?.tag===1?text(v.payload):\"\";else node.value=text(v)};const read=()=>{if(kind===\"bool\")return!!node.checked;if(kind===\"radio\")return node.checked?{tag:1,payload:node.value}:s.value;if(kind===\"option-float\")return node.value===\"\"?{tag:0,payload:null}:{tag:1,payload:Number(node.value)};return node.value};const sync=()=>publish(s,read());node.addEventListener(kind===\"string\"&&node.tagName!==\"SELECT\"?\"input\":\"change\",sync,true);s.listeners.add(draw);draw(s.value)};"
  , "const mountAttribute=(node,kind)=>{const cap=kind===\"class\"?\"Class\":\"Style\",mounted=\"vrDyn\"+cap+\"Mounted\";if(node.dataset[mounted])return;node.dataset[mounted]=\"1\";const make=globalThis.__vrDynamics[Number(node.dataset[\"vrDyn\"+cap])];if(!make)return;const signal=make(decodeCaptures(node.dataset[\"vrDyn\"+cap+\"Captures\"])),base=kind===\"class\"?node.className:node.style.cssText;const draw=()=>{const dynamic=text(signal.read()),combined=dynamic+(base?\" \"+base:\"\");if(kind===\"class\")node.className=combined;else node.style.cssText=combined};signal.subscribe(draw);draw()};"
  , "const mount=(root=document)=>{if(typeof document===\"undefined\")return;prepareSources();for(const node of nodes(root,\"[data-vr-control-source]\"))mountControl(node);for(const node of nodes(root,\"[data-vr-dyn-class]\"))mountAttribute(node,\"class\");for(const node of nodes(root,\"[data-vr-dyn-style]\"))mountAttribute(node,\"style\");for(const node of nodes(root,\"[data-vr-dyn-source]\")){if(node.dataset.vrMounted)continue;node.dataset.vrMounted=\"1\";const s=globalThis.__vrSources[Number(node.dataset.vrDynSource)];if(!s)continue;const draw=v=>{node.innerHTML=text(v);mount(node)};s.listeners.add(draw);draw(s.value)}for(const node of nodes(root,\"[data-vr-dyn]\")){if(node.dataset.vrMounted)continue;node.dataset.vrMounted=\"1\";const make=globalThis.__vrDynamics[Number(node.dataset.vrDyn)];if(!make)continue;const signal=make(captureValues(node));const draw=()=>{node.innerHTML=text(signal.read());mount(node)};signal.subscribe(draw);draw()}for(const node of nodes(root,\"[data-vr-active],[data-vr-script]\")){if(node.dataset.vrMounted)continue;node.dataset.vrMounted=\"1\";const identifier=Number(node.dataset.vrActive??node.dataset.vrScript);const make=globalThis.__vrActives[identifier];if(!make)continue;Promise.resolve(make(captureValues(node))).then(value=>{if(node.dataset.vrActive!==undefined)node.innerHTML=text(value);mount(node)})}};"
  , "const tagNames=new Set(\"dyn active script head title link meta body br span div p strong em b i tt sub sup h1 h2 h3 h4 h5 h6 li ol ul hr pre section article nav aside footer header main meter progress output keygen datalist details dialog menuitem figure figcaption data mark rp rt ruby summary time wbr bdi a img form subform subforms entry hidden textbox password textarea checkbox email search url_ tel color number range date datetime datetime_local month week timeInput upload radio radioOption select option submit image label fieldset legend ctextbox cpassword cemail csearch curl ctel ccolor cnumber crange cdate cdatetime cdatetime_local cmonth cweek ctime button ccheckbox cradio cselect coption ctextarea tabl tr th td thead tbody tfoot dl dt dd\".split(\" \"));"
  , "const inputNames=new Set(\"textbox password email search url_ tel color number range date datetime datetime_local month week timeInput checkbox radioOption hidden upload submit image ctextbox cpassword cemail csearch curl ctel ccolor cnumber crange cdate cdatetime cdatetime_local cmonth cweek ctime ccheckbox cradio\".split(\" \"));const elementName=n=>n===\"tabl\"?\"table\":n===\"cselect\"?\"select\":n===\"coption\"?\"option\":n===\"ctextarea\"?\"textarea\":inputNames.has(n)?\"input\":n;const voidTags=new Set(\"br hr img input link meta\".split(\" \"));"
  , "const inputType=n=>({textbox:\"text\",ctextbox:\"text\",password:\"password\",cpassword:\"password\",email:\"email\",cemail:\"email\",search:\"search\",csearch:\"search\",url_:\"url\",curl:\"url\",tel:\"tel\",ctel:\"tel\",color:\"color\",ccolor:\"color\",number:\"number\",cnumber:\"number\",range:\"range\",crange:\"range\",date:\"date\",cdate:\"date\",datetime:\"datetime\",cdatetime:\"datetime\",datetime_local:\"datetime-local\",cdatetime_local:\"datetime-local\",month:\"month\",cmonth:\"month\",week:\"week\",cweek:\"week\",timeInput:\"time\",ctime:\"time\",checkbox:\"checkbox\",ccheckbox:\"checkbox\",radioOption:\"radio\",cradio:\"radio\",hidden:\"hidden\",upload:\"file\",submit:\"submit\",image:\"image\"})[n];const controlKind=n=>({ctextbox:\"string\",cpassword:\"string\",cemail:\"string\",csearch:\"string\",curl:\"string\",ctel:\"string\",ccolor:\"string\",cdate:\"string\",cdatetime:\"string\",cdatetime_local:\"string\",cmonth:\"string\",cweek:\"string\",ctime:\"string\",ctextarea:\"string\",cnumber:\"option-float\",crange:\"option-float\",ccheckbox:\"bool\",cradio:\"radio\",cselect:\"string\"})[n];"
  , "const literal=value=>typeof value===\"bigint\"?value+\"n\":typeof value===\"number\"||typeof value===\"boolean\"?String(value):value==null?\"null\":typeof value===\"string\"?JSON.stringify(value).replaceAll(\"<\",\"\\\\u003C\"):Array.isArray(value)?\"[\"+value.map(literal).join(\",\")+\"]\":\"{\"+Object.entries(value).map(([k,v])=>JSON.stringify(k)+\":\"+literal(v)).join(\",\")+\"}\";const captureCode=value=>Number.isInteger(value?.clientId)?\"globalThis.__vrSources[\"+value.clientId+\"]\":Number.isInteger(value?.__vrClientClosure?.identifier)?\"globalThis.__vrClosures[\"+value.__vrClientClosure.identifier+\"]([\"+value.__vrClientClosure.captures.map(captureCode).join(\",\")+\"])\":literal(value);const island=(kind,property,value)=>html(\"<span data-vr-\"+kind+\"=\\\"\"+value[property]+\"\\\" data-vr-captures=\\\"\"+escape(\"[\"+(value.__vrCaptures||[]).map(captureCode).join(\",\")+\"]\")+\"\\\"></span>\");"
  , "const renderClientTag=a=>b=>c=>d=>attributes=>descriptor=>child=>{const n=descriptor.__vrTag;if(n===\"dyn\"&&Number.isInteger(attributes.Signal?.__vrDynamic))return island(\"dyn\",\"__vrDynamic\",attributes.Signal);if((n===\"active\"||n===\"script\")&&Number.isInteger(attributes.Code?.__vrActive))return island(n,\"__vrActive\",attributes.Code);const htmlName=elementName(n),kind=controlKind(n),s=attributes.Source,dyn=(option,which)=>{const marker=option?.tag===1?option.payload:null;return Number.isInteger(marker?.__vrDynamic)?\" data-vr-dyn-\"+which+\"=\\\"\"+marker.__vrDynamic+\"\\\" data-vr-dyn-\"+which+\"-captures=\\\"\"+escape(\"[\"+(marker.__vrCaptures||[]).map(captureCode).join(\",\")+\"]\")+\"\\\"\":\"\"};const decorations=(text(a)===\"\"?\"\":\" class=\\\"\"+escape(a)+\"\\\"\")+(text(c)===\"\"?\"\":\" style=\\\"\"+escape(c)+\"\\\"\")+dyn(b,\"class\")+dyn(d,\"style\");const attrs=decorations+Object.entries(attributes||{}).filter(([k])=>k!==\"Signal\"&&k!==\"Code\"&&!(k===\"Source\"&&kind)).map(([k,v])=>{if(k===\"Data\")return text(v)===\"\"?\"\":\" \"+text(v);if(k.startsWith(\"On\")&&Number.isInteger(v?.__vrHandler))return\" \"+k.toLowerCase()+\"=\\\"return globalThis.__vrHandlers[\"+v.__vrHandler+\"]([\"+(v.__vrCaptures||[]).map(value=>escape(captureCode(value))).join(\",\")+\"])(event)\\\"\";const name=k===\"Typ\"?\"type\":k===\"Nam\"?\"name\":k.toLowerCase();if(typeof v===\"boolean\")return v?\" \"+name:\"\";return\" \"+name+\"=\\\"\"+escape(v)+\"\\\"\"}).join(\"\");const binding=kind&&Number.isInteger(s?.clientId)?\" data-vr-control-source=\\\"\"+s.clientId+\"\\\" data-vr-control-kind=\\\"\"+kind+\"\\\"\":\"\",typ=inputType(n);return html(\"<\"+htmlName+(typ?\" type=\\\"\"+typ+\"\\\"\":\"\")+binding+attrs+(voidTags.has(htmlName)?\" />\":\">\"+text(child)+\"</\"+htmlName+\">\"))};"
  , "const basis=(n,staticArguments=[])=>{switch(n){case\"tag\":return renderClientTag;case\"join\":return a=>b=>html(text(a)+text(b));case\"cdata\":return x=>isHtml(x)?x:html(htmlify(x));case\"null\":case\"noStyle\":return html(\"\");case\"minTime\":return fromMicros(0n);case\"alert\":return x=>tx(()=>{globalThis.alert(text(x));return null});case\"confirm\":return x=>tx(()=>!!globalThis.confirm(text(x)));case\"debug\":case\"naughtyDebug\":return x=>tx(()=>{console.debug(text(x));return null});case\"strcat\":return a=>b=>text(a)+text(b);case\"source\":return x=>tx(()=>source(x));case\"get\":return get;case\"set\":return s=>x=>set(s,x);case\"onError\":return handler=>registerHandler(\"error\",handler);case\"onFail\":return handler=>registerHandler(\"fail\",handler);case\"onConnectFail\":return handler=>registerHandler(\"connectFail\",handler);case\"onDisconnect\":return handler=>registerHandler(\"disconnect\",handler);case\"onServerError\":return handler=>registerHandler(\"serverError\",handler);case\"now\":return tx(()=>fromMicros(BigInt(Date.now())*1000n));case\"fresh\":return tx(()=>fresh());case\"currentUrl\":return tx(()=>globalThis.location?.toString?.()??\"\");case\"giveFocus\":return id=>tx(()=>{const node=document.getElementById(text(id));if(!node)throw new Error(\"Tried to give focus to ID not used in document: \"+text(id));node.focus();return null});case\"preventDefault\":return tx(()=>{originalEvent()?.preventDefault?.();return null});case\"stopPropagation\":return tx(()=>{originalEvent()?.stopPropagation?.();return null});case\"onClick\":return handler=>globalEvent(\"click\",handler);case\"onDblclick\":return handler=>globalEvent(\"dblclick\",handler);case\"onContextmenu\":return handler=>globalEvent(\"contextmenu\",handler);case\"onKeydown\":return handler=>globalEvent(\"keydown\",handler);case\"onKeypress\":return handler=>globalEvent(\"keypress\",handler);case\"onKeyup\":return handler=>globalEvent(\"keyup\",handler);case\"onMousedown\":return handler=>globalEvent(\"mousedown\",handler);case\"onMouseenter\":return handler=>globalEvent(\"mouseenter\",handler);case\"onMouseleave\":return handler=>globalEvent(\"mouseleave\",handler);case\"onMousemove\":return handler=>globalEvent(\"mousemove\",handler);case\"onMouseout\":return handler=>globalEvent(\"mouseout\",handler);case\"onMouseover\":return handler=>globalEvent(\"mouseover\",handler);case\"onMouseup\":return handler=>globalEvent(\"mouseup\",handler);default:return tagNames.has(n)?_=>({__vrTag:n}):curryCall(n,staticArguments)}};"
  , "const customTag=n=>_=>({__vrTag:n});"
  , "const extendedCall=(n,a,staticArguments=[])=>{const s=index=>text(a[index]),number=index=>Number(a[index]),big=index=>BigInt(a[index]);switch(n){case\"htmlifyInt\":case\"htmlifyFloat\":case\"htmlifyString\":return html(htmlify(a[0]));case\"htmlifyBool\":return html(a[0]?\"True\":\"False\");case\"htmlifySpecialChar\":return html(\"&#\"+Number(a[0])+\";\");case\"attrifyInt\":case\"attrifyFloat\":return text(a[0]);case\"attrifyBool\":return a[0]?\"True\":\"False\";case\"stringToInt\":return option(integer(a[0]));case\"stringToFloat\":return option(floating(a[0]));case\"stringToChar\":return option(character(a[0]));case\"stringToBool\":return option(s(0)===\"True\"?true:s(0)===\"False\"?false:null);case\"stringToInt_error\":{const v=integer(a[0]);if(v===null)throw new Error(\"Can't parse int: \"+s(0));return v}case\"stringToFloat_error\":{const v=floating(a[0]);if(v===null)throw new Error(\"Can't parse float: \"+s(0));return v}case\"stringToChar_error\":{const v=character(a[0]);if(v===null)throw new Error(\"Can't parse char: \"+s(0));return v}case\"stringToBool_error\":if(s(0)===\"True\")return true;if(s(0)===\"False\")return false;throw new Error(\"Illegal Boolean \"+s(0));case\"stringToTime\":{const v=Date.parse(s(0));return option(Number.isNaN(v)?null:fromMicros(BigInt(v)*1000n))}case\"stringToTime_error\":{const v=Date.parse(s(0));if(Number.isNaN(v))throw new Error(\"Invalid date string: \"+s(0));return fromMicros(BigInt(v)*1000n)}}"
  , "switch(n){case\"strlen\":return BigInt(codepoints(a[0]).length);case\"strlenUtf8\":return BigInt(s(0).length);case\"strlenGe\":return BigInt(codepoints(a[0]).length)>=big(1);case\"str1\":case\"charToString\":return String.fromCodePoint(number(0));case\"strsub\":{const value=codepoints(a[0]),index=number(1);if(index<0||index>=value.length)throw new Error(\"String index \"+index+\" out of bounds\");return value[index].codePointAt(0)}case\"strsubUtf8\":{const value=s(0),index=number(1);if(index<0||index>=value.length)throw new Error(\"String index \"+index+\" out of bounds\");return value.charCodeAt(index)}case\"strsuffix\":{const index=number(1);if(index<0)throw new Error(\"Negative strsuffix bound\");return codepoints(a[0]).slice(index).join(\"\")}case\"strsuffixUtf8\":{const index=number(1);if(index<0)throw new Error(\"Negative strsuffixUtf8 bound\");return s(0).substring(index)}case\"substring\":{const value=codepoints(a[0]),start=number(1),length=number(2);if(start<0)throw new Error(\"substring: Negative start index\");if(length<0)throw new Error(\"substring: Negative length\");if(start+length>value.length)throw new Error(\"substring: Start index plus length is too large\");return value.slice(start,start+length).join(\"\")}case\"strindex\":{const index=codepoints(a[0]).findIndex(value=>value.codePointAt(0)===number(1));return option(index<0?null:BigInt(index))}case\"strsindex\":{const haystack=codepoints(a[0]),needle=codepoints(a[1]);if(needle.length===0)return option(0n);outer:for(let index=0;index+needle.length<=haystack.length;index++){for(let offset=0;offset<needle.length;offset++)if(haystack[index+offset]!==needle[offset])continue outer;return option(BigInt(index))}return option(null)}case\"strchr\":{const value=codepoints(a[0]),index=value.findIndex(character=>character.codePointAt(0)===number(1));return option(index<0?null:value.slice(index).join(\"\"))}case\"strcspn\":{const value=codepoints(a[0]),needles=new Set(codepoints(a[1])),index=value.findIndex(character=>needles.has(character));return BigInt(index<0?value.length:index)}}"
  , "switch(n){case\"islower\":return /^\\p{Lowercase_Letter}$/u.test(String.fromCodePoint(number(0)));case\"isupper\":return /^\\p{Uppercase_Letter}$/u.test(String.fromCodePoint(number(0)));case\"isalpha\":return /^\\p{Alphabetic}$/u.test(String.fromCodePoint(number(0)));case\"isdigit\":return /^\\p{Decimal_Number}$/u.test(String.fromCodePoint(number(0)));case\"isalnum\":return /^[\\p{Alphabetic}\\p{Decimal_Number}]$/u.test(String.fromCodePoint(number(0)));case\"isblank\":return /^(?:\\t|\\p{Zs})$/u.test(String.fromCodePoint(number(0)));case\"isspace\":return /^\\p{White_Space}$/u.test(String.fromCodePoint(number(0)));case\"isxdigit\":return /^[A-Fa-f0-9]$/.test(String.fromCodePoint(number(0)));case\"isprint\":return /^(?:[\\p{L}\\p{M}\\p{N}\\p{P}\\p{S}]|\\p{Zs})$/u.test(String.fromCodePoint(number(0)));case\"tolower\":return String.fromCodePoint(number(0)).toLowerCase().codePointAt(0);case\"toupper\":return String.fromCodePoint(number(0)).toUpperCase().codePointAt(0);case\"ord\":return big(0);case\"chr\":{const value=big(0);if(value<0n||value>0x10ffffn)throw new Error(\"The integer \"+value+\" is not a valid char codepoint\");return Number(value)}case\"floatFromInt\":case\"float\":return number(0);case\"ceil\":return BigInt(Math.ceil(number(0)));case\"trunc\":return BigInt(Math.trunc(number(0)));case\"round\":return BigInt(Math.round(number(0)));case\"floor\":return BigInt(Math.floor(number(0)));case\"pow\":return Math.pow(number(0),number(1));case\"sqrt\":return Math.sqrt(number(0));case\"sin\":return Math.sin(number(0));case\"cos\":return Math.cos(number(0));case\"log\":return Math.log(number(0));case\"exp\":return Math.exp(number(0));case\"asin\":return Math.asin(number(0));case\"acos\":return Math.acos(number(0));case\"atan\":return Math.atan(number(0));case\"atan2\":return Math.atan2(number(0),number(1));case\"abs\":return Math.abs(number(0))}"
  , "switch(n){case\"minTime\":return fromMicros(0n);case\"now\":return tx(()=>fromMicros(BigInt(Date.now())*1000n));case\"eq_time\":return micros(a[0])===micros(a[1]);case\"lt_time\":return micros(a[0])<micros(a[1]);case\"le_time\":return micros(a[0])<=micros(a[1]);case\"timeToString\":return timeFormat(configuredTimeFormat,a[0]);case\"htmlifyTime\":return html(escape(timeFormat(configuredTimeFormat,a[0])));case\"timef\":return timeFormat(s(0),a[1]);case\"addSeconds\":return fromMicros(micros(a[0])+big(1)*1000000n);case\"toSeconds\":return BigInt(Math.round(Number(micros(a[0]))/1000000));case\"diffInSeconds\":return BigInt(Math.round(Number(micros(a[1])-micros(a[0]))/1000000));case\"toMilliseconds\":return BigInt(Math.round(Number(micros(a[0]))/1000));case\"fromMilliseconds\":return fromMicros(big(0)*1000n);case\"diffInMilliseconds\":return BigInt(Math.round(Number(micros(a[1])-micros(a[0]))/1000));case\"fromDatetime\":return fromMicros(BigInt(new Date(number(0),number(1),number(2),number(3),number(4),number(5)).getTime())*1000n);case\"datetimeYear\":return BigInt(timeParts(a[0]).getFullYear());case\"datetimeMonth\":return BigInt(timeParts(a[0]).getMonth());case\"datetimeDay\":return BigInt(timeParts(a[0]).getDate());case\"datetimeHour\":return BigInt(timeParts(a[0]).getHours());case\"datetimeMinute\":return BigInt(timeParts(a[0]).getMinutes());case\"datetimeSecond\":return BigInt(timeParts(a[0]).getSeconds());case\"datetimeDayOfWeek\":return BigInt(timeParts(a[0]).getDay());case\"anchorUrl\":return\"#\"+s(0);case\"currentUrl\":return tx(()=>globalThis.location?.toString?.()??\"\");case\"fresh\":return tx(()=>fresh());case\"giveFocus\":return basis(\"giveFocus\")(a[0]);case\"preventDefault\":return basis(\"preventDefault\");case\"stopPropagation\":return basis(\"stopPropagation\");case\"confirm\":return basis(\"confirm\")(a[0]);case\"debug\":case\"naughtyDebug\":return basis(\"debug\")(a[0]);default:throw new Error(\"Unsupported browser Basis.\"+n)}};"
  , "const call=(n,a,staticArguments=[])=>{switch(n){case\"decodeBytes\":return bytes(a[0]);case\"cdata\":return isHtml(a[0])?a[0]:html(htmlify(a[0]));case\"attrifyString\":return attrify(a[0]);case\"atom\":return css(\"atom\",a[0]);case\"css_url\":return css(\"url\",a[0]);case\"property\":return css(\"property\",a[0]);case\"bless\":return bless(a[0]);case\"checkUrl\":return checkUrl(a[0]);case\"blessData\":{const x=text(a[0]);if(!/^[A-Za-z0-9_-]*$/.test(x))throw new Error(\"Illegal HTML5 data-* attribute: \"+x);return x}case\"intToString\":case\"floatToString\":case\"show_string\":return text(a[0]);case\"boolToString\":return a[0]?\"True\":\"False\";case\"charToString\":case\"str1\":return String.fromCodePoint(Number(a[0]));case\"urlifyString\":return urlify(a[0]);case\"urlifyInt\":return BigInt(a[0]).toString();case\"urlifyFloat\":return text(a[0]);case\"urlifyBool\":return a[0]?\"1\":\"0\";case\"urlifyChar\":return urlify(String.fromCodePoint(Number(a[0])));case\"urlifyTime\":return micros(a[0]).toString();case\"new_client_source\":return source(a[0]);case\"set_client_source\":publish(a[0],a[1]);return null;case\"get_client_source\":return a[0].value;case\"alert\":return basis(n)(a[0]);case\"strlen\":return BigInt(codepoints(a[0]).length);default:return extendedCall(n,a,staticArguments)}};"
  , "const sequence=(x,k)=>tx(async()=>{await run(x);return run(k())});const letValue=(x,k)=>x&&typeof x.then===\"function\"?x.then(k):k(x);"
  , "const closure=(f,c)=>x=>{let y=f;for(const v of c)y=app(y,v);return app(y,x)};"
  , "const redirect=x=>tx(()=>{let target=text(x);if(target.endsWith(\"#\"))target=target.slice(0,-1);globalThis.location=target;return null});"
  , "const typeTag=d=>d.tag===\"ffi\"?d.module+\".\"+d.name:d.tag;const urlify=s=>{s=text(s);if(s===\"\")return\"_\";let r=s[0]===\"_\"?\"_\":\"\";for(const b of new TextEncoder().encode(s)){if(b===32)r+=\"+\";else if(b>=48&&b<=57||b>=65&&b<=90||b>=97&&b<=122)r+=String.fromCharCode(b);else r+=\".\"+b.toString(16).toUpperCase().padStart(2,\"0\")}return r};const unurl=s=>{s=String(s);if(s[0]===\"_\")s=s.slice(1);const out=[];for(let i=0;i<s.length;){if(s[i]===\"+\"){out.push(32);i++}else if(s[i]===\".\"||s[i]===\"%\"){out.push(parseInt(s.slice(i+1,i+3),16));i+=3}else{out.push(...new TextEncoder().encode(s[i++]));}}return new TextDecoder().decode(new Uint8Array(out))};"
  , "const decode=(d,s)=>{const p=String(s).split(\"/\");let i=0;const next=()=>{if(i>=p.length)throw new Error(\"Missing RPC value\");return p[i++]};const go=t=>{switch(typeTag(t)){case\"record\":{if(t.fields.length===0){if(next()!==\"_\")throw new Error(\"Invalid unit RPC value\");return null}const r={};for(const [n,u]of t.fields)r[n]=go(u);return r}case\"datatype\":{const n=next();const c=(dt[t.id]||[]).find(x=>x.name===n);if(!c)throw new Error(\"Invalid RPC constructor\");return{tag:c.tag,payload:c.payload===null?null:go(c.payload)}}case\"option\":{const n=next();return n===\"None\"?{tag:0,payload:null}:n===\"Some\"?{tag:1,payload:go(t.element)}:(()=>{throw new Error(\"Invalid RPC option\")})()}case\"list\":{const n=next();return n===\"Nil\"?{tag:0,payload:null}:n===\"Cons\"?{tag:1,payload:{\"1\":go(t.element),\"2\":go(t)}}:(()=>{throw new Error(\"Invalid RPC list\")})()}case\"Basis.int\":return BigInt(next());case\"Basis.float\":return Number(next());case\"Basis.bool\":return next()===\"1\";case\"Basis.char\":return unurl(next()).codePointAt(0)||0;case\"Basis.time\":{const n=BigInt(next());return{seconds:n/1000000n,microseconds:n%1000000n}}case\"Basis.channel\":return{__vrChannel:unurl(next())};default:return unurl(next())}};const v=go(d);if(i!==p.length)throw new Error(\"Trailing RPC value\");return v};"
  , "const clientHeaders=()=>globalThis.__vrClientId==null||globalThis.__vrClientToken==null?{}:{\"X-Vr-Client\":String(globalThis.__vrClientId),\"X-Vr-Client-Token\":String(globalThis.__vrClientToken)};const xsrfSignature=async()=>{if(globalThis.__vrSig!=null)return String(globalThis.__vrSig);if(typeof document!==\"undefined\"&&document.readyState!==\"complete\"){await new Promise(resolve=>globalThis.addEventListener(\"load\",resolve,{once:true}));if(globalThis.__vrSig!=null)return String(globalThis.__vrSig)}throw new Error(\"Missing cookie signature!\")};const internalUrl=path=>(globalThis.__vrUrlPrefix??\"/\")+\"__vr/\"+path;let disconnectReported=false;const reportDisconnect=error=>{if(disconnectReported)return;disconnectReported=true;runHandlers(\"disconnect\",error?.message??String(error),false)};const reported=error=>{if(error&&(typeof error===\"object\"||typeof error===\"function\"))error.__vrReportedError=true;return error};if(globalThis.__vrClientId!=null&&globalThis.__vrClientToken!=null&&globalThis.fetch){const delay=Math.max(250,Number(globalThis.__vrClientTimeout||60)*500);globalThis.__vrClientHeartbeat??=setInterval(async()=>{try{const response=await fetch(internalUrl(\"client\"),{cache:\"no-store\",headers:clientHeaders()});if(!response.ok)reportDisconnect(new Error(\"Client heartbeat failed with HTTP \"+response.status))}catch(error){reportDisconnect(error)}},delay);globalThis.__vrClientHeartbeat.unref?.()}const serverCall=(url,d,failure,needsSignature)=>tx(async()=>{try{const headers=clientHeaders();if(needsSignature)headers[\"UrWeb-Sig\"]=await xsrfSignature();const response=await fetch(text(url),{method:\"POST\",headers});if(!response.ok){const body=await response.text();throw new Error(body||\"RPC failed with HTTP \"+response.status)}const lines=(await response.text()).split(\"\\n\");if(lines.length!==2)throw new Error(\"Bad RPC response lines\");if(lines[0]!==\"\")(0,eval)(lines[0]);const value=decode(d,lines[1]);return failure===\"error\"?{tag:1,payload:value}:value}catch(error){runHandlers(\"connectFail\",error?.message??String(error),false);if(failure===\"error\")return{tag:0,payload:null};throw reported(error)}});"
  , "const channelRecv=(channel,d)=>tx(async()=>{if(!channel||typeof channel.__vrChannel!==\"string\")throw new TypeError(\"Invalid Ur channel\");const url=internalUrl(\"channel/\")+encodeURIComponent(channel.__vrChannel);for(;;){let response;try{response=await fetch(url,{cache:\"no-store\",headers:clientHeaders()})}catch(error){reportDisconnect(error);throw reported(error)}if(response.status===204){await new Promise(resolve=>setTimeout(resolve,25));continue}if(!response.ok){const body=await response.text(),error=new Error(body||\"Channel receive failed with HTTP \"+response.status);runHandlers(\"serverError\",error.message);throw reported(error)}return decode(d,await response.text())}});const spawn=x=>tx(()=>{Promise.resolve(run(x));return null});const sleep=x=>tx(()=>new Promise(r=>setTimeout(()=>r(null),Number(x))));"
  , "const cut=(r,ks)=>{r={...r};for(const k of ks)delete r[k];return r};const fail=x=>{runHandlers(\"error\",x);const error=new Error(text(x));error.__vrReportedError=true;throw error};const matchFailure=()=>{throw new Error(\"Non-exhaustive Ur pattern match\")};"
  , "const signalReturn=x=>({read:()=>x,subscribe:()=>()=>{}});const signalSource=s=>({read:()=>s.value,subscribe:f=>{s.listeners.add(f);return()=>s.listeners.delete(f)}});const signalBind=(s,k)=>({read:()=>app(k,s.read()).read(),subscribe:f=>{let inner=app(k,s.read()),stopInner=inner.subscribe(f);const outer=()=>{stopInner();inner=app(k,s.read());stopInner=inner.subscribe(f);f()};const stopOuter=s.subscribe(outer);return()=>{stopOuter();stopInner()}}});"
  , "const event=e=>{currentBrowserEvent=e;const buttonTag=[0,2,1][Number(e.button)]??0;return Object.defineProperty({AltKey:!!e.altKey,Button:{tag:buttonTag,payload:null},ClientX:BigInt(e.clientX||0),ClientY:BigInt(e.clientY||0),CtrlKey:!!e.ctrlKey,MetaKey:!!e.metaKey,OffsetX:BigInt(e.offsetX||0),OffsetY:BigInt(e.offsetY||0),ScreenX:BigInt(e.screenX||0),ScreenY:BigInt(e.screenY||0),ShiftKey:!!e.shiftKey,KeyCode:BigInt(e.keyCode||0),Repeat:!!e.repeat},\"__vrEvent\",{value:e})};"
  , "return{app,basis,binary,call,channelRecv,closure,concat:(a,b)=>isHtml(a)||isHtml(b)?html(text(a)+text(b)):text(a)+text(b),customTag,cut,equal,event,fail,force,foreign,foreignCall,get,html,letValue,matchFailure,mount,redirect,run,sequence,serverCall,set,signalBind,signalReturn,signalSource,sleep,spawn,source,unary,write:x=>x};})("
  , renderDatatypeMap context
  , ");"
  ]

eventHandlers :: M.Expr -> [(M.Expr, Bool)]
eventHandlers expression = here <> concatMap eventHandlers (expressionChildren expression)
  where
    here =
      [ (value, functionDepth typ >= 2)
      | (M.StaticName name, value, typ) <- tagAttributeFields expression
      , take 2 name == "On"
      , functionDepth typ >= 1
      ]

dynamicSignals :: M.Expr -> [M.Expr]
dynamicSignals expression = here <> concatMap dynamicSignals (expressionChildren expression)
  where
    here = tagDynamicSignalsHere expression <>
      [ value
      | (M.StaticName "Signal", value, typ) <- tagAttributeFields expression
      , M.TSignal {} <- [locatedValue typ]
      ]

-- A tag's second and fourth runtime operands are optional client signals for
-- dynClass and dynStyle.  They are client roots just like the Signal field of
-- <dyn>, even though the surface syntax places them outside the attributes
-- record.
tagDynamicSignalsHere :: M.Expr -> [M.Expr]
tagDynamicSignalsHere expression = case collectApplications expression of
  (function, [_, dynamicClass, _, dynamicStyle, _, _, _])
    | M.EFfi "Basis" "tag" _ <- locatedValue function ->
        optionSignal dynamicClass <> optionSignal dynamicStyle
  (function, [_, dynamicClass, _, dynamicStyle, _, _])
    | M.EFfi "Basis" "__vr_tag_open" _ <- locatedValue function ->
        optionSignal dynamicClass <> optionSignal dynamicStyle
  _ -> []
  where
    optionSignal option = case locatedValue option of
      M.ESome _ signal -> [signal]
      _ -> []

collectApplications :: M.Expr -> (M.Expr, [M.Expr])
collectApplications expression = go expression []
  where
    go current@(Located at _) arguments = case locatedValue current of
      M.EApp function argument -> go function (argument : arguments)
      M.EFfiApp moduleName name staticArguments applied ->
        (Located at (M.EFfi moduleName name staticArguments), map fst applied <> arguments)
      _ -> (current, arguments)

activeCodeBlocks :: M.Expr -> [M.Expr]
activeCodeBlocks expression = here <> concatMap activeCodeBlocks (expressionChildren expression)
  where
    here =
      [ value
      | (M.StaticName "Code", value, typ) <- tagAttributeFields expression
      , M.TFun {} <- [locatedValue typ]
      ]

tagAttributeFields :: M.Expr -> [(M.StaticArg, M.Expr, M.Type)]
tagAttributeFields expression = case collectApplications expression of
  (function, [_, _, _, _, attributes, _, _])
    | M.EFfi "Basis" "tag" _ <- locatedValue function -> case locatedValue attributes of
        M.ERecord fields -> fields
        _ -> []
  (function, [_, _, _, _, attributes, _])
    | M.EFfi "Basis" "__vr_tag_open" _ <- locatedValue function -> case locatedValue attributes of
        M.ERecord fields -> fields
        _ -> []
  _ -> []

declarationNeedsClientRuntime :: M.Decl -> Bool
declarationNeedsClientRuntime declaration = any needsRuntime
  [ nested
  | expression <- declarationExpressions declaration
  , nested <- expressionDescendants expression
  ]
  where
    needsRuntime expression = case locatedValue expression of
      M.EJavaScript {} -> True
      M.ESignalReturn {} -> True
      M.ESignalBind {} -> True
      M.ESignalSource {} -> True
      M.EServerCall {} -> True
      M.ERecv {} -> True
      _ -> False

functionDepth :: M.Type -> Int
functionDepth typ = case locatedValue typ of
  M.TFun _ range -> 1 + functionDepth range
  _ -> 0

freeRelativeIndices :: M.Expr -> [Int]
freeRelativeIndices = Set.toAscList . collect 0
  where
    collect depth expression = case locatedValue expression of
      M.ERel index
        | index >= depth -> Set.singleton (index - depth)
        | otherwise -> Set.empty
      M.EAbs _ _ _ body -> collect (depth + 1) body
      M.ELet _ _ value body -> collect depth value <> collect (depth + 1) body
      M.ECase scrutinee branches _ _ ->
        collect depth scrutinee
          <> Set.unions
            [ collect (depth + patternBindingsCount pattern') body
            | (pattern', body) <- branches
            ]
      _ -> Set.unions (map (collect depth) (expressionChildren expression))

patternBindingsCount :: M.Pattern -> Int
patternBindingsCount pattern' = case locatedValue pattern' of
  M.PVar {} -> 1
  M.PCon _ _ nested -> maybe 0 patternBindingsCount nested
  M.PRecord fields -> sum [patternBindingsCount nested | (_, nested, _) <- fields]
  M.PSome _ nested -> patternBindingsCount nested
  _ -> 0

declarationExpressions :: M.Decl -> [M.Expr]
declarationExpressions declaration = case locatedValue declaration of
  M.DVal _ _ _ expression _ -> [expression]
  M.DValRec bindings -> [expression | (_, _, _, expression, _) <- bindings]
  M.DTable _ _ primary constraints -> [primary, constraints]
  M.DView _ _ expression -> [expression]
  M.DIndexDynamic table modes -> [table, modes]
  M.DTask schedule body -> [schedule, body]
  M.DPolicy policy -> case policy of
    M.PolicyClient expression -> [expression]
    M.PolicyInsert expression -> [expression]
    M.PolicyDelete expression -> [expression]
    M.PolicyUpdate expression -> [expression]
    M.PolicySequence expression -> [expression]
  M.DPolicyRaw expression -> [expression]
  _ -> []

expressionChildren :: M.Expr -> [M.Expr]
expressionChildren expression = case locatedValue expression of
  M.ECon _ _ payload -> maybe [] pure payload
  M.ESome _ value -> [value]
  M.EFfiApp _ _ _ arguments -> map fst arguments
  M.EApp function argument -> [function, argument]
  M.EAbs _ _ _ body -> [body]
  M.EStaticApp function _ -> [function]
  M.EUnop _ value -> [value]
  M.EBinop _ _ left right -> [left, right]
  M.ERecord fields -> [value | (_, value, _) <- fields]
  M.EField record _ -> [record]
  M.ERecordConcat left right -> [left, right]
  M.ERecordCut record _ -> [record]
  M.ECase scrutinee branches _ _ -> scrutinee : map snd branches
  M.EStrcat left right -> [left, right]
  M.EError message _ -> [message]
  M.EReturnBlob blob mime _ -> maybe [] pure blob <> [mime]
  M.ERedirect value _ -> [value]
  M.EWrite value -> [value]
  M.ESeq first second -> [first, second]
  M.ELet _ _ value body -> [value, body]
  M.EClosure _ captures -> captures
  M.EQuery _ _ _ query body initial -> [query, body, initial]
  M.EDml value _ -> [value]
  M.ENextval value -> [value]
  M.ESetval sequence' value -> [sequence', value]
  M.EUnurlify value _ _ -> [value]
  M.EJavaScript _ value -> [value]
  M.ESignalReturn value -> [value]
  M.ESignalBind signal continuation -> [signal, continuation]
  M.ESignalSource value -> [value]
  M.EServerCall call _ _ _ -> [call]
  M.ERecv channel _ -> [channel]
  M.ESleep value -> [value]
  M.ESpawn value -> [value]
  M.ESqlCache _ _ keys action -> keys <> [action]
  M.ESqlCacheFlush _ flushes action ->
    [key | flush <- flushes, Just key <- M.sqlCacheFlushKeys flush] <> [action]
  _ -> []

expressionDescendants :: M.Expr -> [M.Expr]
expressionDescendants expression = collect expression []
  where
    -- Append to a tail instead of copying each descendant list at every
    -- ancestor of a deeply nested application or HTML expression.
    collect value rest = value : foldr collect rest (expressionChildren value)

-- Expression equality includes its source span.  Indexing candidates by that
-- span therefore skips impossible deep comparisons while retaining exact
-- structural equality for generated nodes that share a synthetic span.
-- Reversing the accumulator preserves Data.List.nub's first-occurrence order.
stableByExpr :: Ord value => (value -> M.Expr) -> [value] -> [value]
stableByExpr expressionOf = reverse . snd . foldl' step (Map.empty, [])
  where
    step accumulated@(seen, values) value =
      let expression = expressionOf value
          at = locatedSpan expression
          bucket = Map.findWithDefault Set.empty at seen
       in if Set.member value bucket
            then accumulated
            else (Map.insert at (Set.insert value bucket) seen, value : values)

expressionReferences :: M.Expr -> Set.Set M.GlobalId
expressionReferences expression = direct <> Set.unions (map expressionReferences (expressionChildren expression))
  where
    direct = case locatedValue expression of
      M.ENamed identifier -> Set.singleton identifier
      M.EClosure identifier _ -> Set.singleton identifier
      _ -> Set.empty

collectDefinitions :: [M.Decl] -> Map.Map M.GlobalId M.Expr
collectDefinitions = Map.fromList . concatMap collect
  where
    collect declaration = case locatedValue declaration of
      M.DVal _ identifier _ expression _ -> [(identifier, expression)]
      M.DValRec bindings -> [(identifier, expression) | (_, identifier, _, expression, _) <- bindings]
      _ -> []

reachableDefinitions
  :: Map.Map M.GlobalId M.Expr
  -> Set.Set M.GlobalId
  -> Set.Set M.GlobalId
reachableDefinitions definitions = go Set.empty
  where
    go done pending = case Set.minView (pending Set.\\ done) of
      Nothing -> done
      Just (identifier, rest) ->
        let dependencies = maybe Set.empty expressionReferences (Map.lookup identifier definitions)
         in go (Set.insert identifier done) (rest <> dependencies)

collectConstructorTags :: [M.Decl] -> Map.Map M.GlobalId Int
collectConstructorTags declarations = Map.fromList
  [ (identifier, tag)
  | declaration <- declarations
  , M.DDatatype definitions <- [locatedValue declaration]
  , (_, _, constructors) <- definitions
  , (tag, (_, identifier, _)) <- zip [0 ..] constructors
  ]

collectDatatypes :: [M.Decl] -> Map.Map M.GlobalId [(String, Int, Maybe M.Type)]
collectDatatypes declarations = Map.fromList
  [ (datatypeIdentifier,
      [(name, tag, payload) | (tag, (name, _, payload)) <- zip [0 ..] constructors])
  | declaration <- declarations
  , M.DDatatype definitions <- [locatedValue declaration]
  , (_, datatypeIdentifier, constructors) <- definitions
  ]

renderDatatypeMap :: ClientContext -> String
renderDatatypeMap context = "({" <> intercalate ","
  [ quote (show (M.unGlobalId identifier)) <> ":[" <> intercalate ","
      [ "{name:" <> quote name <> ",tag:" <> show tag <> ",payload:"
          <> maybe "null" renderType payload <> "}"
      | (name, tag, payload) <- constructors
      ] <> "]"
  | (identifier, constructors) <- Map.toAscList (clientDatatypes context)
  ] <> "})"

renderUrlFilters :: ClientContext -> String
renderUrlFilters context = "[" <> intercalate ","
  [ "{allow:" <> jsBool (filterRuleAction rule == FilterAllow)
      <> ",prefix:" <> jsBool (filterRulePatternKind rule == PrefixPattern)
      <> ",pattern:" <> quote (filterRulePattern rule) <> "}"
  | rule <- clientUrlFilters context
  ] <> "]"

renderType :: M.Type -> String
renderType typ = case locatedValue typ of
  M.TFun domain range -> object "function"
    [("domain", renderType domain), ("range", renderType range)]
  M.TRecord fields ->
    "{tag:\"record\",fields:[" <> intercalate ","
      ["[" <> quote name <> "," <> renderType fieldType <> "]" | (name, fieldType) <- fields]
      <> "]}"
  M.TDatatype identifier -> object "datatype" [("id", show (M.unGlobalId identifier))]
  M.TFfi moduleName name ->
    "{tag:\"ffi\",module:" <> quote moduleName <> ",name:" <> quote name <> "}"
  M.TOption element -> object "option" [("element", renderType element)]
  M.TList element -> object "list" [("element", renderType element)]
  M.TSource -> "{tag:\"source\"}"
  M.TSignal element -> object "signal" [("element", renderType element)]
  where
    object tag fields = "{tag:" <> quote tag
      <> concat ["," <> name <> ":" <> value | (name, value) <- fields] <> "}"

renderStaticList :: [M.StaticArg] -> String
renderStaticList arguments = "[" <> intercalate "," (map renderStatic arguments) <> "]"

renderStatic :: M.StaticArg -> String
renderStatic argument = case argument of
  M.StaticType typ -> object "type" [("value", renderType typ)]
  M.StaticName name -> object "name" [("value", quote name)]
  M.StaticRow fields -> object "row"
    [("fields", "[" <> intercalate ","
      ["[" <> renderStatic name <> "," <> renderStatic value <> "]" | (name, value) <- fields]
      <> "]")]
  M.StaticTuple elements -> object "tuple" [("elements", renderStaticList elements)]
  M.StaticFfi moduleName name arguments ->
    "{tag:\"ffi\",module:" <> quote moduleName <> ",name:" <> quote name
      <> ",arguments:" <> renderStaticList arguments <> "}"
  M.StaticMap -> "{tag:\"map\"}"
  M.StaticBound index -> object "bound" [("index", show index)]
  M.StaticLambda body -> object "lambda" [("body", renderStatic body)]
  M.StaticApply function value -> object "apply"
    [("function", renderStatic function), ("value", renderStatic value)]
  M.StaticProject tuple index -> object "project"
    [("tuple", renderStatic tuple), ("index", show index)]
  M.StaticConcat left right -> object "concat"
    [("left", renderStatic left), ("right", renderStatic right)]
  M.StaticUnit -> "{tag:\"unit\"}"
  where
    object tag fields = "{tag:" <> quote tag
      <> concat ["," <> name <> ":" <> value | (name, value) <- fields] <> "}"

staticName :: Located value -> M.StaticArg -> Generate String
staticName source argument = case argument of
  M.StaticName name -> pure name
  _ -> failure source "client-record" "A client record operation retained a dynamic field name"

foreignFunctions :: ProjectPlan -> Map.Map (String, String) ClientForeignFunction
foreignFunctions plan = Map.fromList
  [ ((moduleName, memberName), ClientForeignFunction
      (modulePrefix <> javascriptName)
      (Map.findWithDefault 1 (moduleName, memberName) arities)
      (Set.member (moduleName, memberName) transactions))
  | directive <- projectDirectives plan
  , projectDirectiveName directive == "jsFunc"
  , let (foreignReference, equalsAndJavaScript) = break (== '=') (projectDirectiveArgument directive)
  , '=' : javascriptName <- [equalsAndJavaScript]
  , let (moduleName, dotAndMember) = break (== '.') foreignReference
  , '.' : memberName <- [dotAndMember]
  , let modulePrefix = case firstDirective "jsModule" of
          Just prefix | not (syntheticInline directive) -> prefix <> "."
          _ -> ""
  ]
  where
    arities = Map.fromList
      [ ((moduleName, memberName), arity)
      | directive <- projectDirectives plan
      , projectDirectiveName directive == "ffiArity"
      , let (foreignReference, equalsAndArity) = break (== '=') (projectDirectiveArgument directive)
      , '=' : rawArity <- [equalsAndArity]
      , [(arity, "")] <- [reads rawArity]
      , let (moduleName, dotAndMember) = break (== '.') foreignReference
      , '.' : memberName <- [dotAndMember]
      ]
    transactions = Set.fromList
      [ (moduleName, memberName)
      | directive <- projectDirectives plan
      , projectDirectiveName directive == "ffiTransaction"
      , let (moduleName, dotAndMember) = break (== '.') (projectDirectiveArgument directive)
      , '.' : memberName <- [dotAndMember]
      ]
    firstDirective name = case
      [projectDirectiveArgument directive
      | directive <- projectDirectives plan
      , projectDirectiveName directive == name] of
      value : _ -> Just value
      [] -> Nothing
    -- Direct FFI modes are appended after elaboration and keep the Ur source
    -- span; project jsFunc mappings instead point at a .urp file.
    syntheticInline directive = not (".urp" `isSuffixOf` spanFile (projectDirectiveSpan directive))

projectScripts :: ProjectPlan -> [String] -> String
projectScripts plan javascriptFiles =
  concatMap externalScript scripts <> embeddedScripts
  where
    scripts =
      [projectDirectiveArgument directive
      | directive <- projectDirectives plan
      , projectDirectiveName directive == "script"]
    externalScript source = "<script src=\"" <> escapeAttribute source <> "\"></script>"
    embeddedScripts = case javascriptFiles of
      [] -> ""
      files -> "<script>" <> concatMap replaceScriptEnd files <> "</script>"

escapeAttribute :: String -> String
escapeAttribute = concatMap $ \character -> case character of
  '&' -> "&amp;"
  '<' -> "&lt;"
  '>' -> "&gt;"
  '"' -> "&quot;"
  '\'' -> "&#39;"
  _ -> [character]

replaceScriptEnd :: String -> String
replaceScriptEnd source = case source of
  [] -> []
  '<' : '/' : 's' : 'c' : 'r' : 'i' : 'p' : 't' : rest -> "<\\/script" <> replaceScriptEnd rest
  character : rest -> character : replaceScriptEnd rest

jsBool :: Bool -> String
jsBool value = if value then "true" else "false"

renderPrimitive :: Primitive -> String
renderPrimitive primitive = case primitive of
  PrimInt value -> show value <> "n"
  PrimFloat value -> show value
  PrimChar value -> show value
  PrimString HtmlString value -> "rt.html(rt.call(\"decodeBytes\",[\"" <> hexBytes value <> "\"]))"
  PrimString _ value -> "rt.call(\"decodeBytes\",[\"" <> hexBytes value <> "\"])"

hexBytes :: ByteString.ByteString -> String
hexBytes = concatMap hex . ByteString.unpack
  where
    hex byte = case showHex byte "" of
      [digit] -> ['0', digit]
      digits -> digits

globalName :: M.GlobalId -> String
globalName identifier = "g[" <> show (M.unGlobalId identifier) <> "]"

fresh :: String -> Generate Code
fresh purpose = do
  index <- get
  put (index + 1)
  pure (codeText ("vr_" <> purpose <> "_" <> show index))

quote :: String -> String
quote value = '"' : concatMap escape value <> "\""
  where
    escape character = case character of
      '"' -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      _ | ord character < 0x20 -> "\\u" <> pad4 (showHex (ord character) "")
      _ -> [character]
    pad4 digits = replicate (4 - length digits) '0' <> digits

capitalize :: String -> String
capitalize [] = []
capitalize (first : rest) = toUpper first : rest

failure :: Located value -> String -> String -> Generate result
failure source code message =
  StateT (const (Left (diagnostic BackendPhase code (locatedSpan source) message)))
