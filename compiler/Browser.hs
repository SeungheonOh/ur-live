-- | Standalone browser target. Reuses Vr's Mono expression lowering, but does
-- not emit server routes, SQL, native shims, RPC, or the server runtime.
module Browser (emitBrowser) where

import Control.Monad (forM, unless)
import Control.Monad.State.Strict (evalStateT)
import Data.List (isSuffixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Vr.Backend.ClientJavaScript as Client
import qualified Vr.Mono.Syntax as M
import Vr.Source

emitBrowser :: Set.Set String -> Maybe String -> M.File -> Either [Diagnostic] String
emitBrowser supported entryModule file = either (Left . (: [])) Right $ do
  mapM_ checkDeclaration declarations
  entry <- case [(identifier, expression) | (name, identifier, _, expression, url) <- bindings,
                    name == "main", maybe ("/main" `isSuffixOf` url) (\m -> url == m <> "/main") entryModule] of
    [value] -> Right value
    _ -> Left (diagnostic BackendPhase "browser-main" noSpan
      "Define fun main () : transaction page. This browser target runs one page, without server routes.")
  let reachable = Client.reachableDefinitions definitions (Set.singleton (fst entry))
      selected = [(identifier, expression) | (_, identifier, _, expression, _) <- bindings,
                    Set.member identifier reachable]
  mapM_ (mapM_ checkExpression . Client.expressionDescendants . snd) selected
  output <- forM selected $ \(identifier, expression) -> do
    body <- Client.finishCode <$> evalStateT (Client.renderExpr context [] expression) 0
    pure (Client.globalName identifier <> " = " <> body <> ";\n")
  pure ("// Compiled by Vr (WebAssembly). Browser-only ECMAScript module.\n"
    <> "import { createRuntime } from './browser-runtime.mjs';\n\n"
    <> "const rt = createRuntime();\nconst g = Object.create(null);\n\n"
    <> concat output
    <> "\nexport async function main() {\n  return rt.text(await rt.run(rt.app("
    <> Client.globalName (fst entry) <> ", {})));\n}\n"
    <> "\nexport async function mount(element) {\n  element.innerHTML = await main();\n  rt.mount(element);\n}\n")
  where
    declarations = M.fileDeclarations file
    bindings = concatMap (\declaration -> case locatedValue declaration of
      M.DVal name identifier typ expression url -> [(name, identifier, typ, expression, url)]
      M.DValRec values -> values
      _ -> []) declarations
    definitions = Client.collectDefinitions declarations
    context = Client.ClientContext
      { Client.clientConstructors = Client.collectConstructorTags declarations
      , Client.clientForeignConstructors = Map.empty
      , Client.clientDefinitions = definitions
      , Client.clientDatatypes = Map.empty
      , Client.contextHandlers = Map.empty
      , Client.contextHandlerCaptures = Map.empty
      , Client.contextDynamics = Map.empty
      , Client.contextDynamicCaptures = Map.empty
      , Client.contextActives = Map.empty
      , Client.contextActiveCaptures = Map.empty
      , Client.clientForeignFunctions = Map.empty
      , Client.clientForeignTags = Set.empty
      , Client.clientUrlFilters = []
      , Client.clientConfiguredTimeFormat = "%c"
      }
    reject at feature = Left (diagnostic BackendPhase "browser-unsupported" at
      (feature <> " is not supported by the standalone browser target (no server, SQL, files, or native FFI)."))
    checkDeclaration declaration = case locatedValue declaration of
      M.DDatatype {} -> Right ()
      M.DVal {} -> Right ()
      M.DValRec {} -> Right ()
      M.DExport {} -> Right () -- Metadata only; no HTTP handlers are emitted.
      M.DStyle {} -> Right ()
      _ -> reject (locatedSpan declaration) "This server declaration"
    checkExpression expression = case locatedValue expression of
      M.EApp {} -> case applications expression of
        (function, arguments) | M.EFfi "Basis" "tag" _ <- locatedValue function,
            _ : dynamicClass : _ : dynamicStyle : _ <- arguments ->
          unless (isNone dynamicClass && isNone dynamicStyle)
            (reject at "Dynamic class/style attributes")
        _ -> Right ()
      M.EFfi moduleName name _ -> checkFfi expression moduleName name
      M.EFfiApp moduleName name _ _ -> checkFfi expression moduleName name
      M.EQuery {} -> reject at "SQL queries"
      M.EDml {} -> reject at "SQL commands"
      M.ENextval {} -> reject at "SQL sequences"
      M.ESetval {} -> reject at "SQL sequences"
      M.ESqlCache {} -> reject at "SQL caching"
      M.ESqlCacheFlush {} -> reject at "SQL caching"
      M.EServerCall {} -> reject at "RPC/server calls"
      M.ERecv {} -> reject at "Server channels"
      M.EReturnBlob {} -> reject at "HTTP blob responses"
      M.ERedirect {} -> reject at "HTTP redirects"
      M.EWrite {} -> reject at "HTTP response writes"
      M.EUnurlify {} -> reject at "Server URL decoding"
      _ -> Right ()
      where at = locatedSpan expression
    checkFfi expression moduleName name =
      unless (moduleName == "Basis" && Set.member name supported)
        (reject (locatedSpan expression) (moduleName <> "." <> name))
    isNone expression = case locatedValue expression of M.ENone {} -> True; _ -> False
    applications = collect []
      where
        collect args expression = case locatedValue expression of
          M.EApp function argument -> collect (argument : args) function
          _ -> (expression, args)
