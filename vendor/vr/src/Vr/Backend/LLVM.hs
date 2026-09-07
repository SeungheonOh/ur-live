{-# LANGUAGE DerivingStrategies #-}

-- | Native backend that emits textual LLVM IR from Vr's target-neutral Mono
-- language.  The supported subset deliberately uses a small platform C ABI
-- for scheduling, channels, HTTP service, allocation, and process effects.
-- Unsupported Mono constructs are rejected with source locations.
module Vr.Backend.LLVM
  ( emitLlvm
  , emitLlvmProject
  , emitLlvmProjectWithAssets
  , emitLlvmProjectWithAssetsAndScripts
  , emitLlvmProjectWithAssetsAndScriptsBytes
  ) where

import Control.Monad (foldM, forM, forM_)
import Control.Monad.State.Strict (StateT, execStateT, gets, lift, modify', runStateT)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Builder as ByteStringBuilder
import qualified Data.ByteString.Char8 as ByteString8
import qualified Data.ByteString.Lazy as LazyByteString
import qualified Data.ByteString.Lazy.Char8 as LazyByteString8
import Data.Char (isAlphaNum, isAscii, toLower)
import Data.Int (Int64)
import Data.List (intercalate, isInfixOf, sortOn, zip4)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Word (Word8)
import Text.Read (readMaybe)
import qualified Vr.Backend.ClientJavaScript as Client
import Vr.Middle (DbMode, Effect (..), ExportKind (..), Sidedness (..))
import qualified Vr.Mono.Server as Server
import qualified Vr.Mono.Syntax as M
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
  , Span
  , StringMode (HtmlString)
  , diagnostic
  , noSpan
  )

data LlvmType
  = I1
  | I8
  | I32
  | I64
  | F64
  | Ptr
  | Function !LlvmType !LlvmType
  | Record ![(String, LlvmType)]
  deriving stock (Eq, Ord, Show)

data Operand = Operand
  { operandType :: !LlvmType
  , operandText :: !String
  }
  deriving stock (Eq, Show)

data FunctionInfo = FunctionInfo
  { functionName :: !String
  , functionParameters :: ![(String, LlvmType)]
  , functionResult :: !LlvmType
  }
  deriving stock (Eq, Show)

data GlobalInfo = GlobalInfo
  { globalName :: !String
  , globalType :: !LlvmType
  }
  deriving stock (Eq, Show)

data ConstructorInfo = ConstructorInfo
  { constructorTag :: !Int
  , constructorPayload :: !(Maybe M.Type)
  }

data DatatypeInfo = DatatypeInfo
  { datatypeConstructors :: ![(String, M.GlobalId, Maybe M.Type)]
  }

data ForeignInfo = ForeignInfo
  { foreignModuleName :: !String
  , foreignMemberName :: !String
  , foreignSourceType :: !M.Type
  , foreignIsTransactional :: !Bool
  }

data NativeTask
  = InitializeTask !M.Expr
  | ClientLeavesTask !M.Expr
  | PeriodicTask !Int64 !M.Expr

data NativeEndpoint = NativeEndpoint
  { endpointUrl :: !ByteString.ByteString
  , endpointValue :: !M.GlobalId
  , endpointPostOnly :: !Bool
  , endpointExtern :: !Bool
  , endpointHasClient :: !Bool
  , endpointNeedsPush :: !Bool
  , endpointArguments :: ![M.Type]
  , endpointRpcResult :: !(Maybe M.Type)
  , endpointXsrfTransport :: !NativeXsrfTransport
  , endpointXsrfValidate :: !Bool
  , endpointPageNeedsSignature :: !Bool
  , endpointSource :: !M.Decl
  }

data NativeXsrfTransport
  = NativeXsrfNone
  | NativeXsrfForm !ByteString.ByteString
  | NativeXsrfRpc

data NativeFilter = NativeFilter
  { filterKind :: !ByteString.ByteString
  , filterAllows :: !Bool
  , filterPrefix :: !Bool
  , filterPattern :: !ByteString.ByteString
  }

data DatabaseSystem
  = DatabasePostgres
  | DatabaseMySQL
  | DatabaseSQLite
  deriving stock (Eq, Show)

data ModuleContext = ModuleContext
  { moduleFunctions :: !(Map.Map M.GlobalId FunctionInfo)
  , moduleGlobals :: !(Map.Map M.GlobalId GlobalInfo)
  , moduleGlobalOrder :: ![M.GlobalId]
  , moduleConstructors :: !(Map.Map M.GlobalId ConstructorInfo)
  , moduleDatatypes :: !(Map.Map M.GlobalId DatatypeInfo)
  , moduleForeignFunctions :: !(Map.Map (String, String) ForeignInfo)
  , moduleForeignCodecs :: !(Set.Set (String, String))
  , moduleForeignConstructors :: !(Map.Map (String, String, String) Server.ForeignConstructor)
  , moduleUrls :: !(Map.Map M.GlobalId ByteString.ByteString)
  , moduleUrlArguments :: !(Map.Map M.GlobalId [M.Type])
  , moduleClientHandlers :: !(Map.Map M.Expr Int)
  , moduleClientCaptures :: !(Map.Map M.Expr [Int])
  , moduleClientCaptureTypes :: !(Map.Map M.Expr [M.Type])
  , moduleClientDynamics :: !(Map.Map M.Expr Int)
  , moduleDynamicCaptures :: !(Map.Map M.Expr [Int])
  , moduleDynamicCaptureTypes :: !(Map.Map M.Expr [M.Type])
  , moduleClientActives :: !(Map.Map M.Expr Int)
  , moduleActiveCaptures :: !(Map.Map M.Expr [Int])
  , moduleActiveCaptureTypes :: !(Map.Map M.Expr [M.Type])
  , moduleClientClosures :: !(Map.Map M.Expr Int)
  , moduleClosureCaptures :: !(Map.Map M.Expr [Int])
  , moduleClosureCaptureTypes :: !(Map.Map M.Expr [M.Type])
  , moduleStrings :: !(Map.Map ByteString.ByteString (Int, Int))
  , moduleDatabaseSystem :: !DatabaseSystem
  , moduleMangleSql :: !Bool
  , moduleCheckDeadlines :: !Bool
  }

data CodegenState = CodegenState
  { codegenNextRegister :: !Int
  , codegenInstructions :: ![String]
  , codegenLocals :: ![Operand]
  , codegenCurrentBlock :: !String
  , codegenHelperPrefix :: !String
  , codegenNextHelper :: !Int
  , codegenHelpers :: ![String]
  }

type Codegen = StateT CodegenState (Either Diagnostic)

-- | Emit one LLVM module without project assets.  The generated entry point
-- follows the C ABI and invokes initialize tasks, registers periodic tasks,
-- and starts HTTP service when exports are present.
emitLlvm :: M.File -> Either [Diagnostic] String
emitLlvm monoFile =
  let plan = ProjectPlan "" "" [] [] []
   in case Server.serverSideProblems plan monoFile of
        problems@(_ : _) -> Left problems
        [] -> case emitModule plan [] [] monoFile of
          Left problem -> Left [problem]
          Right output -> Right (LazyByteString8.unpack output)

-- | Validate target-relevant project directives before emitting LLVM. Loader
-- and middle-end directives have already done their work; every other
-- directive is rejected until the native runtime implements its semantics.
emitLlvmProject :: ProjectPlan -> M.File -> Either [Diagnostic] String
emitLlvmProject plan = emitLlvmProjectWithAssets plan []

-- | Emit a project after its static assets have been loaded by the IO-facing
-- driver.  A @file@ directive is accepted only when each directive has a
-- corresponding byte payload.
emitLlvmProjectWithAssets :: ProjectPlan -> [ProjectAsset] -> M.File -> Either [Diagnostic] String
emitLlvmProjectWithAssets plan assets = emitLlvmProjectWithAssetsAndScripts plan assets []

emitLlvmProjectWithAssetsAndScripts
  :: ProjectPlan
  -> [ProjectAsset]
  -> [String]
  -> M.File
  -> Either [Diagnostic] String
emitLlvmProjectWithAssetsAndScripts plan assets javascriptFiles monoFile =
  LazyByteString8.unpack <$>
    emitLlvmProjectWithAssetsAndScriptsBytes plan assets javascriptFiles monoFile

-- | Byte-oriented LLVM emission for build drivers.  Textual LLVM is commonly
-- many megabytes even for a modest Ur source file.  Keeping that output as a
-- lazy byte string avoids the 20-to-30-byte-per-character cost of Haskell's
-- linked-list 'String' representation while it is hashed, cached, and written
-- to Clang.  The String API above remains available for compatibility.
emitLlvmProjectWithAssetsAndScriptsBytes
  :: ProjectPlan
  -> [ProjectAsset]
  -> [String]
  -> M.File
  -> Either [Diagnostic] LazyByteString.ByteString
emitLlvmProjectWithAssetsAndScriptsBytes plan assets javascriptFiles monoFile =
  case Server.serverSideProblems plan monoFile of
    problems@(_ : _) -> Left problems
    [] -> case unsupported <> missingAssets <> missingJavaScript of
      [] -> case emitModule plan assets javascriptFiles monoFile of
        Left problem -> Left [problem]
        Right output -> Right output
      directives -> Left (map unsupportedDirective directives)
  where
    -- These settings have either already affected project loading/the shared
    -- middle end, or only select output paths in the reference driver.  They
    -- carry no additional native runtime behavior at this point.
    supported =
      [ "library", "path", "ffi", "include", "link", "linker", "coreInline", "neverInline", "file", "database"
      , "filecache"
      , "limit", "minHeap"
      , "rewrite", "debug", "profile", "exe", "sql", "sigfile", "noXsrfProtection"
      , "safeGetDefault", "safeGet", "effectful", "benignEffectful"
      , "clientOnly", "serverOnly", "clientToServer", "lessSafeFfi", "noMangleSql"
      , "html5", "xhtml"
      , "timeFormat"
      , "timeout"
      , "mimeTypes"
      , "dbms"
      , "allow", "deny", "prefix", "onError"
      , "script", "jsFile", "jsModule", "jsFunc"
      , "ffiArity", "ffiTransaction"
      ]
    unsupported = filter ((`notElem` supported) . projectDirectiveName) (projectDirectives plan)
      <> filter unsupportedLimit (projectDirectives plan)
    unsupportedLimit directive = projectDirectiveName directive == "limit"
      && case words (projectDirectiveArgument directive) of
        [kind, _] -> kind `notElem`
          ["inputs", "clients", "headers", "page", "heap", "script", "subinputs", "cleanup", "messages", "deltas", "transactionals", "globals", "database", "time"]
        _ -> True
    fileDirectives = filter ((== "file") . projectDirectiveName) (projectDirectives plan)
    missingAssets = if length fileDirectives == length assets then [] else fileDirectives
    javascriptDirectives = filter ((== "jsFile") . projectDirectiveName) (projectDirectives plan)
    missingJavaScript =
      if length javascriptDirectives == length javascriptFiles then [] else javascriptDirectives
    unsupportedDirective directive =
      diagnostic BackendPhase "llvm-project-directive" (projectDirectiveSpan directive)
        (directiveMessage (projectDirectiveName directive))
    directiveMessage name
      | name == "file" = "A static file directive was not loaded into the native compilation"
      | name == "jsFile" = "A JavaScript file directive was not loaded into the browser bundle"
      | name == "limit" = "The LLVM native backend does not yet implement this resource-limit category"
      | otherwise =
          "The LLVM native backend does not implement the '" <> name <> "' project directive"

emitModule
  :: ProjectPlan
  -> [ProjectAsset]
  -> [String]
  -> M.File
  -> Either Diagnostic LazyByteString.ByteString
emitModule plan assets javascriptFiles monoFile = do
  client <- Client.compileClientProgram plan javascriptFiles monoFile
  functions <- collectFunctions declarations
  globals <- collectGlobals declarations
  constructors <- collectConstructors declarations
  let datatypes = collectDatatypes declarations
      serverIds = Server.serverReachableDefinitionIds plan monoFile
      clientOnlyIds = Server.clientOnlyDefinitionIds plan declarations
  rawEndpoints <- collectEndpoints (M.fileFunctionModes monoFile) declarations
  let directives = projectDirectives plan
      foreignFunctions = Map.restrictKeys
        (collectForeignFunctions directives declarations)
        (Server.serverForeignNames plan monoFile)
      foreignCodecs = Set.fromList
        [ (moduleName, typeName)
        | directive <- directives
        , projectDirectiveName directive == "clientToServer"
        , let (moduleName, suffix) = break (== '.') (projectDirectiveArgument directive)
        , '.' : typeName <- [suffix]
        , moduleName /= "Basis"
        ]
      foreignDatatypeConstructors = Server.serverForeignConstructors plan monoFile
      foreignConstructorMap = Map.fromList
        [ ( ( Server.foreignConstructorModule constructor
            , Server.foreignConstructorDatatype constructor
            , Server.foreignConstructorName constructor
            )
          , constructor
          )
        | constructor <- foreignDatatypeConstructors
        ]
      urlPrefix = nativeUrlPrefix directives
      urlPrefixBytes = ByteString8.pack urlPrefix
      xsrfExemptions = Set.fromList
        [ ByteString8.pack (projectDirectiveArgument directive)
        | directive <- directives
        , projectDirectiveName directive == "noXsrfProtection"
        ]
      endpoints = map (configureEndpointXsrf xsrfExemptions . mountEndpoint urlPrefix) rawEndpoints
      mountedAssets = map (mountAsset urlPrefix) assets
      filters = nativeFilters plan
      timeFormat = case reverse
        [ByteString8.pack (projectDirectiveArgument directive)
        | directive <- directives
        , projectDirectiveName directive == "timeFormat"] of
          format : _ -> format
          [] -> ByteString8.pack "%c"
      clientTimeout = case reverse
        [ read (projectDirectiveArgument directive) :: Int64
        | directive <- directives
        , projectDirectiveName directive == "timeout"] of
          seconds : _ -> seconds
          [] -> 60
      inputLimit = case
        [ read amount :: Int64
        | directive <- directives
        , projectDirectiveName directive == "limit"
        , ["inputs", amount] <- [words (projectDirectiveArgument directive)]
        ] of
          limit : _ -> Just limit
          [] -> Nothing
      resourceLimits =
        [ (ByteString8.pack kind, read amount :: Int64)
        | kind <- ["clients", "headers", "page", "heap", "script", "subinputs", "cleanup", "messages", "deltas", "transactionals", "globals", "database", "time"]
        , directive : _ <-
            [ [ candidate
              | candidate <- directives
              , projectDirectiveName candidate == "limit"
              , case words (projectDirectiveArgument candidate) of
                  selected : _ -> selected == kind
                  [] -> False
              ]
            ]
        , [_, amount] <- [words (projectDirectiveArgument directive)]
        ]
      minimumHeap = maximum
        (0 :
          [ read (projectDirectiveArgument directive) :: Int64
          | directive <- directives
          , projectDirectiveName directive == "minHeap"
          ])
      (applicationInputSlots, applicationInputCount) = allocateApplicationInputs endpoints
      signatureFile = case
        [ ByteString8.pack (projectDirectiveArgument directive)
        | directive <- directives
        , projectDirectiveName directive == "sigfile"
        ] of
          path : _ -> Just path
          [] -> Nothing
      xsrfCookies =
        [ ByteString8.pack name
        | declaration <- declarations
        , M.DCookie name <- [locatedValue declaration]
        ]
      xsrfEnvironment = map ByteString8.pack (collectXsrfEnvironment plan declarations)
      assetStrings asset = [projectAssetUri asset, projectAssetMime asset, projectAssetBytes asset]
      endpointStrings endpoint = endpointUrl endpoint : case endpointXsrfTransport endpoint of
        NativeXsrfForm field -> [field]
        _ -> []
      filterStrings filter' = [filterKind filter', filterPattern filter']
      databaseConnections =
        [ ByteString8.pack connection
        | declaration <- declarations
        , M.DDatabaseRaw connection <- [locatedValue declaration]
        ]
      databaseSystemName = case
        [ projectDirectiveArgument directive
        | directive <- directives
        , projectDirectiveName directive == "dbms"
        ] of
          selected : _ -> selected
          [] -> "postgres"
      databaseSystem = parseDatabaseSystem databaseSystemName
      mangleSqlNames = not (any ((== "noMangleSql") . projectDirectiveName) directives)
      databaseSystemBytes = ByteString8.pack databaseSystemName
      fileCache = case
        [ ByteString8.pack (projectDirectiveArgument directive)
        | directive <- directives
        , projectDirectiveName directive == "filecache"
        ] of
          directory : _ -> Just directory
          [] -> Nothing
      databaseInitializers = databaseInitializationStrings databaseSystem
        (maybe False (const True) fileCache) declarations
      databaseSchemaStrings = concatMap (schemaDeclarationStrings databaseSystem mangleSqlNames) declarations
      capabilityStrings = map ByteString8.pack ["url", "mime", "requestHeader", "responseHeader", "env", "meta", "data"]
      clientScript = ByteString8.pack (Client.clientScript client)
      clientAttributeStrings =
        [ ByteString8.pack fragment
        | (name, identifier) <- Client.clientHandlerAttributes client
        , fragment <-
            [ clientHandlerAttribute name identifier
            , clientHandlerAttributeStart name identifier
            ]
        ]
      clientDynamicStrings =
        [ ByteString8.pack (clientDynamicTagStart identifier)
        | identifier <- Map.elems (Client.clientDynamics client)
        ]
      clientDynamicAttributeStrings =
        [ ByteString8.pack (clientDynamicAttributeStart kind identifier)
        | identifier <- Map.elems (Client.clientDynamics client)
        , kind <- ["class", "style"]
        ]
      clientActiveStrings =
        [ ByteString8.pack (clientIslandTagStart name identifier)
        | identifier <- Map.elems (Client.clientActives client)
        , name <- ["active", "script"]
        ]
      clientClosureStrings =
        [ ByteString8.pack (clientClosureStart identifier)
        | identifier <- Map.elems (Client.clientClosures client)
        ]
      clientCaptureTypeStrings = concatMap (concatMap typeStrings . concat . Map.elems)
        [ Client.clientHandlerCaptureTypes client
        , Client.clientDynamicCaptureTypes client
        , Client.clientActiveCaptureTypes client
        , Client.clientClosureCaptureTypes client
        ]
      clientTagStrings = map (ByteString8.pack . show)
        (0 : 1 : concat
          [ [0 .. length datatypeConstructors' - 1]
          | declaration <- declarations
          , M.DDatatype definitions <- [locatedValue declaration]
          , (_, _, datatypeConstructors') <- definitions
          ])
      foreignTagStrings = concat
        [ let (opening, openingEnd, closing) = htmlTagFragments (htmlElementName name)
           in map ByteString8.pack [opening, openingEnd, closing]
        | declaration <- declarations
        , M.DForeign _ name _ <- [locatedValue declaration]
        ]
      strings = stableNub (map ByteString8.pack
        [ "", " ", "(", "/", "#", "_", "null", "{", "}", "({tag:", ",payload:", "})", "\"1\":", "\"2\":"
        , " name=\"", "\"", "None", "Some", "Some/", "Nil", "Cons", "Cons/"
        , "<span data-vr-dyn-source=\"", "\"></span>", "]\"></span>", "]\"", ","
        , "globalThis.__vrSources[", "]", "])(event)\"", "\"></span>"
        , " data-vr-control-source=\"", "\" data-vr-control-kind=\""
        , "string", "option-float", "bool", "radio"
        , " class=\"", " style=\""
        , "Invalid URL encoding", "NULL", "INSERT INTO ", " DEFAULT VALUES", " (", ") VALUES (", ", ", ")"
        , "SELECT ", "DISTINCT ", "0", "T_", ".", " AS vr__", "vr__", "__", " AS ", " AS \"", "\"", " AS `", "`", " AS T_"
        , " FROM ", " WHERE ", " GROUP BY ", " HAVING ", " ORDER BY "
        , " JOIN ", " LEFT JOIN ", " RIGHT JOIN ", " FULL JOIN ", " ON "
        , " LIMIT ", " OFFSET ", "RANDOM()", " DESC"
        , "NOT", "AND", "OR", "+", "-", "*", "%", "=", "<>", "<", "<=", ">", ">=", "LIKE"
        , " IS NULL)", "COALESCE(", "(CASE WHEN ", " THEN ", " ELSE ", " END)", "COUNT(*)"
        , "COUNT", "AVG", "SUM", "MAX", "MIN"
        , "length", "lower", "upper", "similarity", "<->"
        , "vr_trigram_similarity", "vr_trigram_distance"
        , "PARTITION BY ", " OVER (", "RANK()"
        , "(unixepoch('now') * 1000000)"
        , "DELETE FROM ", "UPDATE ", " SET ", " WHERE ", " = "
        , "CREATE TABLE IF NOT EXISTS ", "CREATE VIEW IF NOT EXISTS ", "CREATE OR REPLACE VIEW ", " AS "
        , "CONSTRAINT ", "_pkey PRIMARY KEY (", "UNIQUE (", "CHECK "
        , "FOREIGN KEY (", ") REFERENCES ", " ON DELETE ", " ON UPDATE "
        , "RESTRICT", "CASCADE", "NO ACTION", "SET NULL"
        , "<input type=\"hidden\" name=\".b\" value=\""
        , "<input type=\"hidden\" name=\".s\" value=\""
        , "<input type=\"hidden\" name=\".i\" value=\"1\" />"
        , "\" />", "<input type=\"hidden\" name=\".e\" value=\"1\" />"
        ] <> [timeFormat, clientScript, urlPrefixBytes, ByteString8.pack "])"]
          <> maybe [] pure signatureFile <> xsrfCookies <> xsrfEnvironment <> map fst resourceLimits
          <> maybe [] pure fileCache
          <> [databaseSystemBytes] <> databaseConnections <> databaseInitializers <> databaseSchemaStrings <> capabilityStrings
          <> clientAttributeStrings <> clientDynamicStrings <> clientDynamicAttributeStrings
          <> clientActiveStrings <> clientClosureStrings <> clientCaptureTypeStrings <> clientTagStrings
          <> foreignTagStrings <> concatMap datatypeUrlStrings declarations
          <> concatMap declarationStrings declarations <> concatMap declarationTypeStrings declarations
          <> concatMap assetStrings mountedAssets <> concatMap endpointStrings endpoints
          <> concatMap filterStrings filters)
      stringTable = Map.fromList (zipWith (\bytes index -> (bytes, (index, ByteString.length bytes + 1))) strings [0 ..])
      urls = Map.fromList [(endpointValue endpoint, endpointUrl endpoint) | endpoint <- endpoints]
      urlArguments = Map.fromList [(endpointValue endpoint, endpointArguments endpoint) | endpoint <- endpoints]
      context = ModuleContext functions globals
        (filter (`Set.member` serverIds) (globalOrder declarations))
        constructors datatypes foreignFunctions foreignCodecs foreignConstructorMap urls urlArguments
        (Client.clientHandlers client) (Client.clientHandlerCaptures client) (Client.clientHandlerCaptureTypes client)
        (Client.clientDynamics client) (Client.clientDynamicCaptures client) (Client.clientDynamicCaptureTypes client)
        (Client.clientActives client) (Client.clientActiveCaptures client) (Client.clientActiveCaptureTypes client)
        (Client.clientClosures client) (Client.clientClosureCaptures client) (Client.clientClosureCaptureTypes client)
        stringTable databaseSystem mangleSqlNames checkDeadlines
      -- Closed applications cannot mutate the runtime time limit through C.
      -- Without a configured positive limit, recursive deadline calls are
      -- no-ops. Keeping them opaque would prevent LLVM optimizing the loop.
      checkDeadlines = maybe False (/= 0) (lookup (ByteString8.pack "time") resourceLimits)
        || not (Map.null foreignFunctions && Set.null foreignCodecs && Map.null foreignConstructorMap)
        || any ((`elem` ["include", "ffi", "link", "linker"]) . projectDirectiveName) directives
      onError = case reverse
        [(declaration, identifier) | declaration <- declarations, M.DOnError identifier <- [locatedValue declaration]] of
          handler : _ -> Just handler
          [] -> Nothing
  case [endpoint | endpoint <- endpoints, Set.member (endpointValue endpoint) clientOnlyIds] of
    endpoint : _ -> backendFailure (endpointSource endpoint) "llvm-placement"
      "An exported server handler depends on a client-only operation"
    [] -> pure ()
  foreignDeclarations <- mapM renderForeignDeclaration (Map.elems foreignFunctions)
  valueDefinitions <- fmap concat (mapM (lowerValueDeclarationExcept clientOnlyIds context) declarations)
  tasks <- collectTasks declarations
  taskDefinitions <- fmap concat (mapM (uncurry (lowerTask context)) (zip [0 ..] tasks))
  endpointDefinitions <- fmap concat (mapM
    (\(index, endpoint) -> lowerEndpoint context applicationInputSlots index endpoint)
    (zip [0 ..] endpoints))
  errorHandlerDefinitions <- case onError of
    Just handler -> lowerErrorHandler context handler
    Nothing -> pure []
  schemaDefinitions <- fmap concat (mapM (uncurry (lowerSchemaDeclaration context)) (zip [0 ..] declarations))
  let schemaInitializers =
        [ index
        | (index, declaration) <- zip [0 :: Int ..] declarations
        , isSchemaInitializer databaseSystem mangleSqlNames declaration
        ]
  let header =
        [ "; Generated by Vr's LLVM backend"
        , "source_filename = \"vr-generated\""
        , ""
        , "@stderr = external global ptr"
        , "declare i32 @fputs(ptr, ptr)"
        , "declare i32 @fputc(i32, ptr)"
        , "declare i32 @strcmp(ptr, ptr)"
        , "declare i64 @strlen(ptr)"
        , "declare ptr @memcpy(ptr, ptr, i64)"
        , "declare noalias ptr @malloc(i64)"
        , "declare void @free(ptr)"
        , "declare ptr @vr_runtime_alloc(i64)"
        , "declare ptr @vr_runtime_alloc_value(i64)"
        , "declare void @vr_runtime_release(ptr)"
        , "declare void @vr_runtime_spawn(ptr, ptr)"
        , "declare void @vr_runtime_periodic(i64, ptr, ptr)"
        , "declare void @vr_runtime_clients_set_timeout(i64)"
        , "declare void @vr_runtime_set_input_limit(i64)"
        , "declare void @vr_runtime_set_application_input_count(i64)"
        , "declare void @vr_runtime_add_application_input(ptr, i64)"
        , "declare void @vr_runtime_set_limit(ptr, i64)"
        , "declare void @vr_runtime_set_min_heap(i64)"
        , "declare void @vr_runtime_check_deadline()"
        , "declare void @vr_runtime_xsrf_set_sigfile(ptr)"
        , "declare void @vr_runtime_xsrf_add_cookie(ptr)"
        , "declare void @vr_runtime_xsrf_add_environment(ptr)"
        , "declare void @vr_runtime_xsrf_initialize()"
        , "declare void @vr_runtime_http_set_url_prefix(ptr)"
        , "declare void @vr_runtime_client_leaves_add(ptr, ptr)"
        , "declare void @vr_runtime_wait()"
        , "declare void @vr_runtime_sleep_ms(i64)"
        , "declare void @vr_runtime_database_configure(ptr, ptr)"
        , "declare void @vr_runtime_database_transaction_begin()"
        , "declare void @vr_runtime_database_transaction_finish(i1)"
        , "declare void @vr_runtime_database_exec(ptr)"
        , "declare void @vr_runtime_database_initialize(ptr)"
        , "declare void @vr_runtime_database_schema_done()"
        , "declare ptr @vr_runtime_database_try_exec(ptr)"
        , "declare ptr @vr_runtime_sql_string(ptr)"
        , "declare ptr @vr_runtime_sql_bool(i1)"
        , "declare ptr @vr_runtime_sql_client(ptr)"
        , "declare ptr @vr_runtime_sql_channel(ptr)"
        , "declare ptr @vr_runtime_sql_blob(ptr)"
        , "declare ptr @vr_runtime_sql_time(ptr)"
        , "declare ptr @vr_runtime_sql_clause(ptr, ptr, i1)"
        , "declare ptr @vr_runtime_sql_comma(ptr, ptr)"
        , "declare ptr @vr_runtime_sql_join(ptr, ptr, ptr, ptr)"
        , "declare ptr @vr_runtime_sql_binary(ptr, ptr, ptr)"
        , "declare ptr @vr_runtime_database_prepare(ptr)"
        , "declare i1 @vr_runtime_database_step(ptr)"
        , "declare void @vr_runtime_database_finalize(ptr)"
        , "declare i1 @vr_runtime_database_column_is_null(ptr, i64)"
        , "declare i64 @vr_runtime_database_column_int(ptr, i64)"
        , "declare double @vr_runtime_database_column_float(ptr, i64)"
        , "declare ptr @vr_runtime_database_column_text(ptr, i64)"
        , "declare ptr @vr_runtime_database_column_blob(ptr, i64)"
        , "declare ptr @vr_runtime_database_column_time(ptr, i64)"
        , "declare ptr @vr_runtime_database_unalias(ptr)"
        , "declare i64 @vr_runtime_database_nextval(ptr)"
        , "declare void @vr_runtime_database_setval(ptr, i64)"
        , "declare void @vr_runtime_file_cache_configure(ptr)"
        , "declare void @vr_runtime_file_cache_store(ptr)"
        , "declare ptr @vr_runtime_file_cache_check(ptr)"
        , "declare i1 @vr_runtime_file_cache_missed()"
        , "declare ptr @vr_runtime_sql_cache_check(i64, i64, ptr)"
        , "declare void @vr_runtime_sql_cache_store(i64, i64, ptr, ptr)"
        , "declare void @vr_runtime_sql_cache_flush(i64, i64, ptr)"
        , "declare ptr @vr_runtime_channel_new()"
        , "declare void @vr_runtime_channel_send(ptr, ptr, ptr)"
        , "declare ptr @vr_runtime_channel_recv(ptr)"
        , "declare ptr @vr_runtime_channel_id(ptr)"
        , "declare ptr @vr_runtime_channel_lookup(ptr)"
        , "declare ptr @vr_runtime_javascript_channel(ptr)"
        , "declare ptr @vr_runtime_channel_lookup_public(i32, i32)"
        , "declare ptr @vr_runtime_channel_from_sql(i64)"
        , "declare i32 @vr_runtime_channel_client(ptr)"
        , "declare i32 @vr_runtime_channel_number(ptr)"
        , "declare i32 @vr_runtime_client_number(ptr)"
        , "declare ptr @vr_runtime_client_from_number(i32)"
        , "declare i64 @vr_runtime_rand()"
        , "declare void @vr_runtime_fail(ptr) noreturn"
        , "declare i64 @vr_runtime_div_int(i64, i64)"
        , "declare i64 @vr_runtime_mod_int(i64, i64)"
        , "declare i64 @vr_runtime_pow_int(i64, i64)"
        , "declare double @vr_runtime_pow_float(double, double)"
        , "declare ptr @vr_runtime_read_int(ptr)"
        , "declare ptr @vr_runtime_read_float(ptr)"
        , "declare ptr @vr_runtime_read_char(ptr)"
        , "declare ptr @vr_runtime_read_bool(ptr)"
        , "declare i64 @vr_runtime_read_int_error(ptr)"
        , "declare double @vr_runtime_read_float_error(ptr)"
        , "declare i32 @vr_runtime_read_char_error(ptr)"
        , "declare i1 @vr_runtime_read_bool_error(ptr)"
        , "declare i1 @vr_runtime_eq_time(ptr, ptr)"
        , "declare i1 @vr_runtime_lt_time(ptr, ptr)"
        , "declare i1 @vr_runtime_le_time(ptr, ptr)"
        , "declare void @vr_runtime_set_time_format(ptr)"
        , "declare ptr @vr_runtime_now()"
        , "declare ptr @vr_runtime_min_time()"
        , "declare ptr @vr_runtime_add_seconds(ptr, i64)"
        , "declare i64 @vr_runtime_to_seconds(ptr)"
        , "declare i64 @vr_runtime_diff_in_seconds(ptr, ptr)"
        , "declare i64 @vr_runtime_to_milliseconds(ptr)"
        , "declare ptr @vr_runtime_from_milliseconds(i64)"
        , "declare i64 @vr_runtime_diff_in_milliseconds(ptr, ptr)"
        , "declare ptr @vr_runtime_timef(ptr, ptr)"
        , "declare ptr @vr_runtime_time_to_string(ptr)"
        , "declare ptr @vr_runtime_read_time(ptr)"
        , "declare ptr @vr_runtime_read_time_error(ptr)"
        , "declare ptr @vr_runtime_read_utc(ptr)"
        , "declare ptr @vr_runtime_from_datetime(i64, i64, i64, i64, i64, i64)"
        , "declare i64 @vr_runtime_datetime_year(ptr)"
        , "declare i64 @vr_runtime_datetime_month(ptr)"
        , "declare i64 @vr_runtime_datetime_day(ptr)"
        , "declare i64 @vr_runtime_datetime_hour(ptr)"
        , "declare i64 @vr_runtime_datetime_minute(ptr)"
        , "declare i64 @vr_runtime_datetime_second(ptr)"
        , "declare i64 @vr_runtime_datetime_day_of_week(ptr)"
        , "declare i1 @vr_runtime_isalnum(i32)"
        , "declare i1 @vr_runtime_isalpha(i32)"
        , "declare i1 @vr_runtime_isblank(i32)"
        , "declare i1 @vr_runtime_iscntrl(i32)"
        , "declare i1 @vr_runtime_isdigit(i32)"
        , "declare i1 @vr_runtime_isgraph(i32)"
        , "declare i1 @vr_runtime_islower(i32)"
        , "declare i1 @vr_runtime_isprint(i32)"
        , "declare i1 @vr_runtime_ispunct(i32)"
        , "declare i1 @vr_runtime_isspace(i32)"
        , "declare i1 @vr_runtime_isupper(i32)"
        , "declare i1 @vr_runtime_isxdigit(i32)"
        , "declare i32 @vr_runtime_tolower(i32)"
        , "declare i32 @vr_runtime_toupper(i32)"
        , "declare i1 @vr_runtime_iscodepoint(i64)"
        , "declare i32 @vr_runtime_chr(i64)"
        , "declare void @vr_runtime_http_set_error_handler(ptr)"
        , "declare void @vr_runtime_http_set_client_script(ptr)"
        , "declare ptr @vr_runtime_current_url()"
        , "declare ptr @vr_runtime_current_query_string()"
        , "declare ptr @vr_runtime_current_client()"
        , "declare i1 @vr_runtime_current_url_has_post()"
        , "declare i1 @vr_runtime_current_url_has_query_string()"
        , "declare ptr @vr_runtime_fresh_id()"
        , "declare ptr @vr_runtime_javascript_string(ptr)"
        , "declare ptr @vr_runtime_javascript_int(i64)"
        , "declare ptr @vr_runtime_javascript_float(double)"
        , "declare ptr @vr_runtime_javascript_bool(i1)"
        , "declare ptr @vr_runtime_javascript_char(i32)"
        , "declare ptr @vr_runtime_javascript_closure(ptr)"
        , "declare ptr @vr_runtime_current_context()"
        , "declare ptr @vr_runtime_client_source_new(ptr)"
        , "declare void @vr_runtime_client_source_set(ptr, ptr)"
        , "declare double @ceil(double)"
        , "declare double @trunc(double)"
        , "declare double @round(double)"
        , "declare double @floor(double)"
        , "declare double @sqrt(double)"
        , "declare double @sin(double)"
        , "declare double @cos(double)"
        , "declare double @log(double)"
        , "declare double @exp(double)"
        , "declare double @asin(double)"
        , "declare double @acos(double)"
        , "declare double @atan(double)"
        , "declare double @atan2(double, double)"
        , "declare double @fabs(double)"
        , "declare void @vr_runtime_http_add_route(ptr, i1, i1, i1, i1, i1, i32, ptr, i1, i1, ptr)"
        , "declare void @vr_runtime_http_add_asset(ptr, ptr, ptr, i64)"
        , "declare void @vr_runtime_http_serve()"
        , "declare ptr @vr_runtime_html_escape(ptr)"
        , "declare ptr @vr_runtime_html_tag_open(ptr)"
        , "declare ptr @vr_runtime_attrify_string(ptr)"
        , "declare ptr @vr_runtime_css_atom(ptr)"
        , "declare ptr @vr_runtime_css_url(ptr)"
        , "declare ptr @vr_runtime_css_property(ptr)"
        , "declare ptr @vr_runtime_get_cookie(ptr)"
        , "declare void @vr_runtime_set_cookie(ptr, ptr, ptr, ptr, i1)"
        , "declare void @vr_runtime_clear_cookie(ptr, ptr)"
        , "declare ptr @vr_runtime_urlify_int(i64)"
        , "declare ptr @vr_runtime_urlify_float(double)"
        , "declare ptr @vr_runtime_urlify_string(ptr)"
        , "declare ptr @vr_runtime_urlify_bool(i1)"
        , "declare ptr @vr_runtime_urlify_char(i32)"
        , "declare ptr @vr_runtime_urlify_time(ptr)"
        , "declare i64 @vr_runtime_unurlify_int(ptr)"
        , "declare ptr @vr_runtime_show_float(double)"
        , "declare ptr @vr_runtime_show_bool(i1)"
        , "declare ptr @vr_runtime_show_char(i32)"
        , "declare i64 @vr_runtime_strlen(ptr)"
        , "declare i64 @vr_runtime_strlen_utf8(ptr)"
        , "declare i1 @vr_runtime_strlen_ge(ptr, i64)"
        , "declare i32 @vr_runtime_strsub(ptr, i64)"
        , "declare i32 @vr_runtime_strsub_utf8(ptr, i64)"
        , "declare ptr @vr_runtime_strsuffix(ptr, i64)"
        , "declare ptr @vr_runtime_strsuffix_utf8(ptr, i64)"
        , "declare ptr @vr_runtime_strchr(ptr, i32)"
        , "declare i64 @vr_runtime_strindex(ptr, i32)"
        , "declare i64 @vr_runtime_strsindex(ptr, ptr)"
        , "declare i64 @vr_runtime_strcspn(ptr, ptr)"
        , "declare ptr @vr_runtime_substring(ptr, i64, i64)"
        , "declare void @vr_runtime_filter_add(ptr, i1, i1, ptr)"
        , "declare ptr @vr_runtime_check_capability(ptr, ptr, i1)"
        , "declare ptr @vr_runtime_get_header(ptr)"
        , "declare void @vr_runtime_set_header(ptr, ptr)"
        , "declare ptr @vr_runtime_get_env(ptr)"
        , "declare ptr @vr_runtime_render_form(ptr, ptr, ptr)"
        , "declare ptr @vr_runtime_render_input(ptr, ptr, ptr)"
        , "declare ptr @vr_runtime_get_form_field(ptr)"
        , "declare ptr @vr_runtime_get_form_file(ptr)"
        , "declare ptr @vr_runtime_get_indexed_form_field(ptr, i64, ptr, i1)"
        , "declare ptr @vr_runtime_get_indexed_form_file(ptr, i64)"
        , "declare void @uw_enter_subform(ptr, i32)"
        , "declare void @uw_leave_subform(ptr)"
        , "declare i32 @uw_enter_subforms(ptr, i32)"
        , "declare i32 @uw_next_entry(ptr)"
        , "declare i32 @vr_runtime_form_char(ptr)"
        , "declare ptr @vr_runtime_file_name(ptr)"
        , "declare ptr @vr_runtime_file_mime_type(ptr)"
        , "declare ptr @vr_runtime_file_data(ptr)"
        , "declare ptr @vr_runtime_post_type(ptr)"
        , "declare ptr @vr_runtime_post_data(ptr)"
        , "declare i64 @vr_runtime_post_length(ptr)"
        , "declare ptr @vr_runtime_first_form_field(ptr)"
        , "declare ptr @vr_runtime_field_name(ptr)"
        , "declare ptr @vr_runtime_field_value(ptr)"
        , "declare ptr @vr_runtime_remaining_fields(ptr)"
        , "declare ptr @vr_runtime_get_url_component(i64)"
        , "declare ptr @vr_runtime_next_url_component()"
        , "declare ptr @vr_runtime_remaining_url_components()"
        , "declare void @vr_runtime_consume_url_components(i64)"
        , "declare i1 @vr_runtime_url_components_done()"
        , "declare void @vr_runtime_require_url_components_done()"
        , "declare void @vr_runtime_unurlify_begin(ptr)"
        , "declare ptr @vr_runtime_next_unurlify_component()"
        , "declare ptr @vr_runtime_remaining_unurlify_components()"
        , "declare void @vr_runtime_consume_unurlify_components(i64)"
        , "declare void @vr_runtime_require_consumed_components(ptr, i64)"
        , "declare void @vr_runtime_require_unurlify_done()"
        , "declare void @vr_runtime_expect_url_component(ptr, ptr)"
        , "declare double @vr_runtime_unurlify_float(ptr)"
        , "declare ptr @vr_runtime_unurlify_string(ptr)"
        , "declare i1 @vr_runtime_unurlify_bool(ptr)"
        , "declare i32 @vr_runtime_unurlify_char(ptr)"
        , "declare ptr @vr_runtime_unurlify_time(ptr)"
        , "declare ptr @vr_runtime_text_blob(ptr)"
        , "declare ptr @vr_runtime_text_of_blob(ptr)"
        , "declare i64 @vr_runtime_blob_size(ptr)"
        , "declare void @vr_runtime_return_blob(ptr, ptr)"
        , "declare void @vr_runtime_redirect(ptr)"
        , "declare void @vr_runtime_clear_page()"
        , "declare void @vr_runtime_write_page(ptr)"
        , "declare void @vr_runtime_write_int(i64)"
        , "declare void @vr_runtime_write_html(ptr)"
        , "declare ptr @vr_runtime_get_page()"
        , "declare ptr @vr_runtime_page_blob()"
        , "declare i64 @vr_runtime_page_mark()"
        , "declare ptr @vr_runtime_page_take(i64)"
        , "declare void @llvm.trap() cold noreturn nounwind"
        ]
      stringDefinitions = map (uncurry renderStringDefinition) (Map.toList stringTable)
      databaseConnection = case reverse databaseConnections of
        connection : _ -> Just connection
        [] -> Nothing
      mainDefinition = renderMain context timeFormat clientScript urlPrefixBytes clientTimeout inputLimit resourceLimits minimumHeap applicationInputSlots applicationInputCount signatureFile xsrfCookies xsrfEnvironment fileCache databaseSystemBytes databaseConnection databaseInitializers schemaInitializers filters tasks endpoints mountedAssets (maybe False (const True) onError)
      foreignCodecDeclarations = concatMap renderForeignCodecDeclarations (Set.toAscList foreignCodecs)
      foreignConstructorDeclarations = concatMap renderForeignConstructorDeclarations foreignDatatypeConstructors
  pure (renderLinesWithBuilders
    (header <> foreignDeclarations <> foreignCodecDeclarations <> foreignConstructorDeclarations)
    stringDefinitions
    ([""] <> valueDefinitions <> schemaDefinitions <> taskDefinitions
      <> endpointDefinitions <> errorHandlerDefinitions <> [mainDefinition]))
  where
    declarations = M.fileDeclarations monoFile
    isSchemaInitializer database mangle declaration = case locatedValue declaration of
      M.DTable {} -> True
      M.DView {} -> True
      M.DIndex table modes -> case databaseIndexCommand database mangle table modes of
        Just _ -> True
        Nothing -> False
      _ -> False

renderLinesWithBuilders
  :: [String]
  -> [ByteStringBuilder.Builder]
  -> [String]
  -> LazyByteString.ByteString
renderLinesWithBuilders before builders after = ByteStringBuilder.toLazyByteString
  ( lineBuilders before
    <> foldMap (<> ByteStringBuilder.char8 '\n') builders
    <> lineBuilders after
  )
  where
    lineBuilders = foldMap (\line -> ByteStringBuilder.stringUtf8 line <> ByteStringBuilder.char8 '\n')

collectFunctions :: [M.Decl] -> Either Diagnostic (Map.Map M.GlobalId FunctionInfo)
collectFunctions = foldM declaration Map.empty
  where
    declaration known source = case locatedValue source of
      M.DVal name identifier typ expression _ ->
        case functionShape expression of
          Just parameters -> insertFunction source known name identifier parameters typ
          Nothing -> pure known
      M.DValRec bindings -> foldM (binding source) known bindings
      _ -> pure known
    binding source known (name, identifier, typ, expression, _) = case functionShape expression of
      Just parameters -> insertFunction source known name identifier parameters typ
      Nothing -> backendFailure source "llvm-recursive-value" "A recursive LLVM binding must lower to a first-order function"

collectGlobals :: [M.Decl] -> Either Diagnostic (Map.Map M.GlobalId GlobalInfo)
collectGlobals = foldM declaration Map.empty
  where
    declaration known source = case locatedValue source of
      M.DVal name identifier typ expression _
        | Nothing <- functionShape expression -> do
            lowered <- lowerTypeAt (locatedSpan source) typ
            pure (Map.insert identifier (GlobalInfo (llvmGlobalName name identifier) lowered) known)
      _ -> pure known

globalOrder :: [M.Decl] -> [M.GlobalId]
globalOrder declarations =
  [ identifier
  | source <- declarations
  , M.DVal _ identifier _ expression _ <- [locatedValue source]
  , Nothing <- [functionShape expression]
  ]

-- The generated Ur/Web signer includes only literal environment-variable
-- names that remain reachable from server-side Mono code.
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
          M.EPrim (PrimString _ bytes) -> Set.singleton (ByteString8.unpack bytes)
          _ -> Set.empty

collectConstructors :: [M.Decl] -> Either Diagnostic (Map.Map M.GlobalId ConstructorInfo)
collectConstructors = foldM declaration Map.empty
  where
    declaration known source = case locatedValue source of
      M.DDatatype datatypes -> pure (foldl insertDatatype known datatypes)
      _ -> pure known
    insertDatatype known (_, _, constructors) =
      foldl insertConstructor known (zip [0 ..] constructors)
    insertConstructor known (tag, (_, identifier, payload)) =
      Map.insert identifier (ConstructorInfo tag payload) known

collectDatatypes :: [M.Decl] -> Map.Map M.GlobalId DatatypeInfo
collectDatatypes declarations = Map.fromList
  [ (identifier, DatatypeInfo constructors)
  | declaration <- declarations
  , M.DDatatype definitions <- [locatedValue declaration]
  , (_, identifier, constructors) <- definitions
  ]

collectForeignFunctions
  :: [ProjectDirective]
  -> [M.Decl]
  -> Map.Map (String, String) ForeignInfo
collectForeignFunctions directives declarations = Map.fromList
  [ ((moduleName, name), ForeignInfo moduleName name typ
      (Set.member (moduleName, name) transactional))
  | declaration <- declarations
  , M.DForeign moduleName name typ <- [locatedValue declaration]
  ]
  where
    transactional = Set.fromList
      [ (moduleName, memberName)
      | directive <- directives
      , projectDirectiveName directive == "ffiTransaction"
      , let (moduleName, dotAndMember) = break (== '.') (projectDirectiveArgument directive)
      , '.' : memberName <- [dotAndMember]
      ]

foreignRuntimeShape :: ForeignInfo -> Either Diagnostic ([LlvmType], LlvmType)
foreignRuntimeShape info = do
  (sourceDomains, sourceResult) <- foreignSourceShape info
  domains <- mapM (lowerTypeAt at) sourceDomains
  result <- lowerTypeAt at sourceResult
  pure (domains, result)
  where
    at = locatedSpan (foreignSourceType info)

foreignSourceShape :: ForeignInfo -> Either Diagnostic ([M.Type], M.Type)
foreignSourceShape info =
  if foreignIsTransactional info
    then case reverse allDomains of
      unit : rest | isUnitSourceType unit -> pure (reverse rest, result)
      _ -> backendFailureAt (locatedSpan (foreignSourceType info)) "llvm-ffi-type"
        (foreignLabel info <> " is marked effectful but does not return a transaction")
    else pure (allDomains, result)
  where
    (allDomains, result) = unwind (foreignSourceType info)
    unwind typ = case locatedValue typ of
      M.TFun domain range -> let (domains, terminal) = unwind range in (domain : domains, terminal)
      _ -> ([], typ)

isUnitSourceType :: M.Type -> Bool
isUnitSourceType typ = case locatedValue typ of
  M.TRecord [] -> True
  M.TFfi "Basis" "unit" -> True
  _ -> False

renderForeignDeclaration :: ForeignInfo -> Either Diagnostic String
renderForeignDeclaration info = do
  (domains, result) <- foreignSourceShape info
  let at = locatedSpan (foreignSourceType info)
  abiDomains <- mapM (foreignSourceAbiType at) domains
  abiResult <- foreignSourceAbiType at result
  let renderedDomains = zipWith renderForeignDomain domains abiDomains
  pure $ if isIndirectForeignSourceType result
    then "declare void " <> foreignSymbol info
      <> "(ptr sret(" <> renderType abiResult <> "), "
      <> intercalate ", " ("ptr" : renderedDomains) <> ")"
    else "declare " <> renderType abiResult <> " " <> foreignSymbol info
      <> "(" <> intercalate ", " ("ptr" : renderedDomains) <> ")"

renderForeignDomain :: M.Type -> LlvmType -> String
renderForeignDomain sourceType abiType
  | isIndirectForeignSourceType sourceType =
      "ptr byval(" <> renderType abiType <> ")"
  | otherwise = renderType abiType

isIndirectForeignSourceType :: M.Type -> Bool
isIndirectForeignSourceType typ = case locatedValue typ of
  M.TFfi "Basis" name -> name `elem` ["file", "postBody"]
  _ -> False

foreignSourceAbiType :: Span -> M.Type -> Either Diagnostic LlvmType
foreignSourceAbiType at typ = case locatedValue typ of
  M.TFfi "Basis" "client" -> pure I32
  -- A pair of 32-bit fields occupies one INTEGER-class register in the
  -- x86-64 SysV C ABI used by Vr's generated objects.
  M.TFfi "Basis" "channel" -> pure I64
  M.TFfi "Basis" "time" -> pure (Record [("seconds", I64), ("microseconds", I32)])
  M.TFfi "Basis" "blob" -> pure (Record [("size", I64), ("data", Ptr)])
  M.TFfi "Basis" "file" -> pure (Record
    [ ("name", Ptr)
    , ("type", Ptr)
    , ("data", Record [("size", I64), ("data", Ptr)])
    ])
  M.TFfi "Basis" "postBody" -> pure foreignPostBodyAbiType
  _ -> foreignAbiType <$> lowerTypeAt at typ

foreignPostBodyAbiType :: LlvmType
foreignPostBodyAbiType = Record
  [("type", Ptr), ("data", Ptr), ("length", I64)]

foreignAbiType :: LlvmType -> LlvmType
foreignAbiType typ = case typ of
  I1 -> I32
  I8 -> I32
  other -> other

foreignSymbol :: ForeignInfo -> String
foreignSymbol info =
  (if foreignNeedsNativeShim info then "@vr_ffi_" else "@uw_")
    <> foreignCIdentifier (foreignModuleName info)
    <> "_" <> foreignCIdentifier (foreignMemberName info)

foreignNeedsNativeShim :: ForeignInfo -> Bool
foreignNeedsNativeShim info = any isAbstract (result : domains)
  where
    (domains, result) = unwind (foreignSourceType info)
    unwind typ = case locatedValue typ of
      M.TFun domain range -> let (rest, terminal) = unwind range in (domain : rest, terminal)
      _ -> ([], typ)
    isAbstract typ = case locatedValue typ of
      M.TFfi moduleName _ -> moduleName /= "Basis"
      _ -> False

foreignLabel :: ForeignInfo -> String
foreignLabel info = foreignModuleName info <> "." <> foreignMemberName info

datatypeUrlStrings :: M.Decl -> [ByteString.ByteString]
datatypeUrlStrings declaration = case locatedValue declaration of
  M.DDatatype definitions -> concat
    [ concatMap constructorStrings constructors
    | (_, _, constructors) <- definitions
    ]
  _ -> []
  where
    constructorStrings (name, _, payload) =
      [ByteString8.pack name] <> [ByteString8.pack (name <> "/") | Just _ <- [payload]]

collectEndpoints :: [(M.GlobalId, Sidedness, DbMode)] -> [M.Decl] -> Either Diagnostic [NativeEndpoint]
collectEndpoints modes declarations = mapM make
  [ (source, kind, url, identifier, arguments, result, pageNeedsSignature)
  | source <- declarations
  , M.DExport kind url identifier arguments result pageNeedsSignature <- [locatedValue source]
  ]
  where
    make (source, kind, url, identifier, arguments, result, pageNeedsSignature) = case kind of
      Link _ -> pure (endpoint source False False Nothing NativeXsrfNone pageNeedsSignature url identifier arguments)
      Action effect -> do
        transport <- case effect of
          ReadCookieWrite -> NativeXsrfForm . ByteString8.pack <$> actionSignatureField source arguments
          _ -> pure NativeXsrfNone
        pure (endpoint source True False Nothing transport pageNeedsSignature url identifier arguments)
      Rpc effect -> pure (endpoint source True False (Just result)
        (if effect == ReadCookieWrite then NativeXsrfRpc else NativeXsrfNone)
        pageNeedsSignature url identifier arguments)
      Extern _ -> pure (endpoint source True True Nothing NativeXsrfNone pageNeedsSignature url identifier arguments)
    endpoint source postOnly external rpcResult transport pageNeedsSignature url identifier arguments = NativeEndpoint
      { endpointUrl = ByteString8.pack (ensureLeadingSlash url)
      , endpointValue = identifier
      , endpointPostOnly = postOnly
      , endpointExtern = external
      , endpointHasClient = placement identifier /= ServerOnly
      , endpointNeedsPush = placement identifier == ServerAndPullAndPush
      , endpointArguments = arguments
      , endpointRpcResult = rpcResult
      , endpointXsrfTransport = transport
      , endpointXsrfValidate = False
      , endpointPageNeedsSignature = pageNeedsSignature
      , endpointSource = source
      }
    actionSignatureField source arguments = case reverse (initOrEmpty arguments) of
      formType : _ -> case locatedValue formType of
        M.TRecord fields -> pure (choose (Set.fromList (map fst fields)) "Sig" (0 :: Int))
        _ -> backendFailure source "llvm-xsrf-form"
          "The submitted argument of a cookie-writing action is not a record"
      [] -> backendFailure source "llvm-xsrf-form"
        "A cookie-writing action has no submitted record argument"
    initOrEmpty [] = []
    initOrEmpty values = init values
    choose fields candidate suffix
      | not (Set.member candidate fields) = candidate
      | otherwise = choose fields ("Sig" <> show suffix) (suffix + 1)
    placement identifier = case [side | (candidate, side, _) <- modes, candidate == identifier] of
      side : _ -> side
      [] -> ServerOnly
    ensureLeadingSlash value = case value of
      '/' : _ -> value
      _ -> '/' : value

insertFunction
  :: M.Decl
  -> Map.Map M.GlobalId FunctionInfo
  -> String
  -> M.GlobalId
  -> [(String, M.Type)]
  -> M.Type
  -> Either Diagnostic (Map.Map M.GlobalId FunctionInfo)
insertFunction source known name identifier parameters declaredType = do
  parameterTypes <- mapM (lowerTypeAt (locatedSpan source) . snd) parameters
  result <- functionResultType (locatedSpan source) (length parameters) declaredType
  let symbol = llvmGlobalName name identifier
  pure (Map.insert identifier (FunctionInfo symbol (zip (map fst parameters) parameterTypes) result) known)

functionResultType :: Span -> Int -> M.Type -> Either Diagnostic LlvmType
functionResultType at parameterCount source = go parameterCount source
  where
    go remaining current
      | remaining == 0 = lowerTypeAt at current
      | otherwise = case locatedValue current of
          M.TFun _ range -> go (remaining - 1) range
          _ -> backendFailureAt at "llvm-function-type" "Function binding has fewer function arrows than lambdas"

functionShape :: M.Expr -> Maybe [(String, M.Type)]
functionShape expression = case locatedValue expression of
  M.EAbs name domain _ body -> Just ((name, domain) : maybe [] id (functionShape body))
  _ -> Nothing

lowerValueDeclaration :: ModuleContext -> M.Decl -> Either Diagnostic [String]
lowerValueDeclaration context source = case locatedValue source of
  M.DForeign {} -> pure []
  M.DVal name identifier _ expression _ -> case functionShape expression of
    Just _ -> lowerFunction context source False name identifier expression
    Nothing -> lowerGlobalValue context source name identifier expression
  M.DValRec bindings -> fmap concat (mapM (\(name, identifier, _, expression, _) -> lowerFunction context source True name identifier expression) bindings)
  M.DDatatype {} -> pure []
  M.DExport {} -> pure []
  M.DTable {} -> pure []
  M.DSequence {} -> pure []
  M.DView {} -> pure []
  M.DIndex {} -> pure []
  M.DIndexDynamic {} -> backendFailure source "llvm-index" "Dynamic database index lowering is not implemented"
  M.DDatabase {} -> pure []
  M.DDatabaseRaw {} -> pure []
  M.DJavaScript {} -> backendFailure source "llvm-javascript" "JavaScript declarations cannot be emitted by the native backend"
  M.DCookie {} -> pure []
  M.DStyle {} -> pure []
  -- Policies are compile-time inputs to Ur/Web's optional information-flow
  -- pass.  Cjrize drops them before code generation, so the normal native
  -- path must do the same after Mono has retained their structured form.
  M.DPolicy {} -> pure []
  M.DPolicyRaw {} -> pure []
  M.DOnError {} -> pure []
  M.DTask {} -> pure []

-- Client helper functions remain in Mono so that the browser generator can
-- compile them, but they must not be translated to native machine code.  In
-- particular, helpers lifted from event-handler lets may contain primitives
-- such as get_client_source that have no meaningful server result type.
lowerValueDeclarationExcept
  :: Set.Set M.GlobalId
  -> ModuleContext
  -> M.Decl
  -> Either Diagnostic [String]
lowerValueDeclarationExcept clientOnly context source = case locatedValue source of
  M.DVal _ identifier _ _ _ | Set.member identifier clientOnly -> pure []
  M.DValRec bindings -> fmap concat . mapM
    (\(name, identifier, _, expression, _) -> lowerFunction context source True name identifier expression) $
    [binding | binding@(_, identifier, _, _, _) <- bindings, not (Set.member identifier clientOnly)]
  _ -> lowerValueDeclaration context source

lowerSchemaDeclaration :: ModuleContext -> Int -> M.Decl -> Either Diagnostic [String]
lowerSchemaDeclaration context index source = case locatedValue source of
  M.DTable name fields primary constraints -> lowerSchemaHelper $ do
    primary' <- lowerExpr context primary
    constraints' <- lowerExpr context constraints
    primaryPieces <- case operandType primary' of
      Ptr -> do
        length' <- emitResult I64 ("call i64 @strlen(" <> typed primary' <> ")")
        present <- emitResult I1 ("icmp ne i64 " <> operandText length' <> ", 0")
        prefix <- lowerStringConcatOperands primary
          (stringOperand context (ByteString8.pack "CONSTRAINT "))
          (stringOperand context (ByteString8.pack name))
        withKey <- lowerStringConcatOperands primary prefix
          (stringOperand context (ByteString8.pack "_pkey PRIMARY KEY ("))
        clause <- emitResult Ptr
          ("call ptr @vr_runtime_sql_clause(" <> typed withKey <> ", "
            <> typed primary' <> ", i1 0)")
        suffix <- chooseSqlText context primary present ")" ""
        (: []) <$> lowerStringConcatOperands primary clause suffix
      I8 -> pure []
      actual -> failCodegen primary "llvm-table-schema"
        ("Primary-key descriptor produced " <> renderType actual)
    constraintPieces <- lowerConstraintPieces context constraints name constraints'
    let indexedFields = schemaIndexedFieldNames primary constraints
    columns <- pure
      [ stringOperand context (ByteString8.pack
          (sqlColumnDefinition (moduleDatabaseSystem context) (moduleMangleSql context)
            indexedFields field))
      | field <- fields
      ]
    definitions <- joinSqlPieces context primary (columns <> primaryPieces <> constraintPieces)
    opened <- lowerStringConcatOperands primary
      (stringOperand context (ByteString8.pack "CREATE TABLE IF NOT EXISTS "))
      (stringOperand context (ByteString8.pack name))
    withParen <- lowerStringConcatOperands primary opened
      (stringOperand context (ByteString8.pack " ("))
    withDefinitions <- lowerStringConcatOperands primary withParen definitions
    command <- lowerStringConcatOperands primary withDefinitions
      (stringOperand context (ByteString8.pack ")"))
    emitInstruction ("call void @vr_runtime_database_initialize(" <> typed command <> ")")
  M.DView name _ query -> do
    lowerSchemaHelper $ do
      query' <- lowerExpr context query
      ensureOperand query Ptr query'
      let viewPrefix = case moduleDatabaseSystem context of
            DatabaseSQLite -> "CREATE VIEW IF NOT EXISTS "
            _ -> "CREATE OR REPLACE VIEW "
      withName <- lowerStringConcatOperands query
        (stringOperand context (ByteString8.pack viewPrefix))
        (stringOperand context (ByteString8.pack name))
      withAs <- lowerStringConcatOperands query withName
        (stringOperand context (ByteString8.pack " AS "))
      command <- lowerStringConcatOperands query withAs query'
      emitInstruction ("call void @vr_runtime_database_initialize(" <> typed command <> ")")
  M.DIndex table modes -> case databaseIndexCommand
      (moduleDatabaseSystem context) (moduleMangleSql context) table modes of
    Just command -> lowerSchemaHelper
      (emitInstruction ("call void @vr_runtime_database_initialize("
        <> typed (stringOperand context (ByteString8.pack command)) <> ")"))
    Nothing -> pure []
  M.DIndexDynamic {} -> backendFailure source "llvm-index"
    "A dynamic database index survived monomorphic lowering"
  _ -> pure []
  where
    lowerSchemaHelper body = do
      let helperName = "vr_schema_" <> show index
          initial = initialCodegenState helperName []
      (_, final) <- runStateT body initial
      let instructions = reverse (codegenInstructions final)
          definition = unlines
            (["define internal void @" <> helperName <> "() {", "entry:"]
              <> map ("  " <>) instructions
              <> ["  ret void", "}", ""])
      pure (definition : reverse (codegenHelpers final))

lowerConstraintPieces
  :: ModuleContext -> M.Expr -> String -> Operand -> Codegen [Operand]
lowerConstraintPieces context source table constraints = case operandType constraints of
  I8 -> pure []
  recordType@(Record fields) -> forM (zip [0 :: Int ..] fields) $ \(index, (name, typ)) -> do
    value <- emitResult typ
      ("extractvalue " <> renderType recordType <> " " <> operandText constraints <> ", " <> show index)
    ensureOperand source Ptr value
    withTable <- lowerStringConcatOperands source
      (stringOperand context (ByteString8.pack "CONSTRAINT "))
      (stringOperand context (ByteString8.pack table))
    withSeparator <- lowerStringConcatOperands source withTable
      (stringOperand context (ByteString8.pack "_"))
    withName <- lowerStringConcatOperands source withSeparator
      (stringOperand context (ByteString8.pack name))
    withSpace <- lowerStringConcatOperands source withName
      (stringOperand context (ByteString8.pack " "))
    lowerStringConcatOperands source withSpace value
  actual -> failCodegen source "llvm-table-schema"
    ("Constraint descriptor produced " <> renderType actual)

lowerGlobalValue :: ModuleContext -> M.Decl -> String -> M.GlobalId -> M.Expr -> Either Diagnostic [String]
lowerGlobalValue context source _name identifier expression = do
  info <- case Map.lookup identifier (moduleGlobals context) of
    Just found -> pure found
    Nothing -> backendFailure source "llvm-global" "Missing collected LLVM global signature"
  let helperName = "vr_init_g" <> show (M.unGlobalId identifier)
      initial = initialCodegenState helperName []
  (value, final) <- runStateT (lowerExpected context (globalType info) expression) initial
  let instructions = reverse (codegenInstructions final)
      storage = globalName info <> " = internal global " <> renderType (globalType info) <> " zeroinitializer"
      initializer = unlines
        (["define internal void @" <> helperName <> "() {", "entry:"]
          <> map ("  " <>) instructions
          <> ["  store " <> typed value <> ", ptr " <> globalName info, "  ret void", "}", ""])
  pure (storage : initializer : reverse (codegenHelpers final))

lowerFunction :: ModuleContext -> M.Decl -> Bool -> String -> M.GlobalId -> M.Expr -> Either Diagnostic [String]
lowerFunction context source recursive name identifier expression = do
  info <- case Map.lookup identifier (moduleFunctions context) of
    Just found -> pure found
    Nothing -> backendFailure source "llvm-function" "Missing collected LLVM function signature"
  let (parameters, body) = peelLambdas expression
      arguments =
        [ Operand typ ("%arg" <> show index)
        | (index, (_, typ)) <- zip [0 :: Int ..] (functionParameters info)
        ]
      initial = initialCodegenState ("vr_g" <> show (M.unGlobalId identifier)) (reverse arguments)
  (result, final) <- runStateT (lowerExpected context (functionResult info) body) initial
  if operandType result /= functionResult info
    then backendFailure source "llvm-type-mismatch"
      ("Expected " <> renderType (functionResult info) <> " but expression produced " <> renderType (operandType result))
    else pure ()
  let signature = intercalate ", "
        [ renderType typ <> " %arg" <> show index
        | (index, (_, typ)) <- zip [0 :: Int ..] (functionParameters info)
        ]
      instructions = reverse (codegenInstructions final)
      bodyLines = ["  call void @vr_runtime_check_deadline()" | recursive && moduleCheckDeadlines context]
        <> map ("  " <>) instructions <> ["  ret " <> typed result]
  if length parameters /= length (functionParameters info)
    then backendFailure source "llvm-function-arity" ("Inconsistent lambda and function type arity for " <> name)
    else pure
      -- Ur bindings are module-local implementation details. HTTP exports and
      -- C callbacks use generated wrappers/function pointers, not these names.
      -- Internal linkage lets LLVM remove inlined copies and specialize calls;
      -- the calling convention and foreign/runtime entry points stay unchanged.
      ( unlines (["define internal " <> renderType (functionResult info) <> " " <> functionName info <> "(" <> signature <> ") {", "entry:"] <> bodyLines <> ["}", ""])
      : reverse (codegenHelpers final)
      )

peelLambdas :: M.Expr -> ([(String, M.Type)], M.Expr)
peelLambdas expression = case locatedValue expression of
  M.EAbs name domain _ body ->
    let (rest, finalBody) = peelLambdas body
     in ((name, domain) : rest, finalBody)
  _ -> ([], expression)

collectTasks :: [M.Decl] -> Either Diagnostic [NativeTask]
collectTasks = fmap reverse . foldM step []
  where
    step done source = case locatedValue source of
      M.DTask schedule body -> case taskSchedule schedule of
        Just InitializeSchedule -> pure (InitializeTask body : done)
        Just ClientLeavesSchedule -> pure (ClientLeavesTask body : done)
        Just (PeriodicSchedule seconds) -> pure (PeriodicTask seconds body : done)
        Nothing -> backendFailure source "llvm-task-schedule"
          "The native backend supports Basis.initialize, Basis.clientLeaves, and Basis.periodic task schedules"
      _ -> pure done

data TaskSchedule = InitializeSchedule | ClientLeavesSchedule | PeriodicSchedule !Int64

taskSchedule :: M.Expr -> Maybe TaskSchedule
taskSchedule expression = case locatedValue expression of
  M.EFfi "Basis" "initialize" [] -> Just InitializeSchedule
  M.EFfi "Basis" "clientLeaves" [] -> Just ClientLeavesSchedule
  M.EApp function argument -> case (locatedValue function, locatedValue argument) of
    (M.EFfi "Basis" "periodic" [], M.EPrim (PrimInt seconds)) -> Just (PeriodicSchedule seconds)
    _ -> Nothing
  _ -> Nothing

lowerTask :: ModuleContext -> Int -> NativeTask -> Either Diagnostic [String]
lowerTask context index task = do
  let body = case task of
        InitializeTask expression -> expression
        ClientLeavesTask expression -> expression
        PeriodicTask _ expression -> expression
      isClientLeaves = case task of ClientLeavesTask {} -> True; _ -> False
      argument = if isClientLeaves then Operand Ptr "%client" else Operand I8 "0"
  let initial = initialCodegenState ("vr_task_" <> show index) []
  final <- execStateT
    (do
      transaction <- applyValue context body [argument]
      _ <- runTransactionOperand context body transaction
      pure ())
    initial
  let instructions = reverse (codegenInstructions final)
      signature = if isClientLeaves then "ptr %client, ptr %environment" else "ptr %environment"
  pure
    ( unlines
        ([ "define internal void @vr_task_" <> show index <> "(" <> signature <> ") {"
         , "entry:"
         , "  call void @vr_runtime_database_transaction_begin()"
         ] <> map ("  " <>) instructions
           <> ["  call void @vr_runtime_database_transaction_finish(i1 true)", "  ret void", "}", ""])
    : reverse (codegenHelpers final)
    )

lowerEndpoint :: ModuleContext -> Map.Map String Int64 -> Int -> NativeEndpoint -> Either Diagnostic [String]
lowerEndpoint context inputSlots index endpoint = do
  if Map.member (endpointValue endpoint) (moduleFunctions context)
      || Map.member (endpointValue endpoint) (moduleGlobals context)
    then pure ()
    else backendFailure (endpointSource endpoint) "llvm-http-export"
      "Export target has no native function value"
  let sourceTypes = case endpointArguments endpoint of
        [] -> []
        arguments -> init arguments
  parameterTypes <- mapM (lowerTypeAt (locatedSpan (endpointSource endpoint))) sourceTypes
  let callSite = Located (locatedSpan (endpointSource endpoint)) (M.ENamed (endpointValue endpoint))
      initial = initialCodegenState ("vr_http_route_" <> show index) []
      lowerHandler = do
        parameters <- mapM (\(parameterIndex, pair) ->
            lowerEndpointArgument context inputSlots endpoint callSite parameterIndex pair)
          (zip [0 :: Int ..] (zip sourceTypes parameterTypes))
        if null (endpointUrlArguments endpoint)
          then pure ()
          else emitInstruction "call void @vr_runtime_require_url_components_done()"
        transaction <- applyDeferredAt context callSite callSite (map Lowered parameters)
        result <- runTransactionOperand context callSite transaction
        case endpointRpcResult endpoint of
          Just resultType -> lowerUrlEncode context callSite resultType result
          Nothing -> case operandType result of
            Ptr -> pure result
            I8 -> pure (stringOperand context ByteString.empty)
            other -> failCodegen callSite "llvm-http-result"
              ("HTTP handler produced " <> renderType other <> " instead of page output")
  (page, final) <- runStateT lowerHandler initial
  let instructions = reverse (codegenInstructions final)
      definition = unlines
        (["define internal ptr @vr_http_route_" <> show index <> "(ptr %request_context) {", "entry:"]
          <> map ("  " <>) instructions
          <> ["  ret " <> typed page, "}", ""])
  pure (definition : reverse (codegenHelpers final))

lowerErrorHandler :: ModuleContext -> (M.Decl, M.GlobalId) -> Either Diagnostic [String]
lowerErrorHandler context (source, identifier) = do
  if Map.member identifier (moduleFunctions context)
      || Map.member identifier (moduleGlobals context)
    then pure ()
    else backendFailure source "llvm-on-error" "Error handler has no native function value"
  let callSite = Located (locatedSpan source) (M.ENamed identifier)
      initial = initialCodegenState "vr_http_on_error" []
      lowerHandler = do
        transaction <- applyDeferredAt context callSite callSite
          [Lowered (Operand Ptr "%message")]
        result <- runTransactionOperand context callSite transaction
        case operandType result of
          Ptr -> pure result
          I8 -> pure (stringOperand context ByteString.empty)
          other -> failCodegen callSite "llvm-on-error-result"
            ("Error handler produced " <> renderType other <> " instead of page output")
  (page, final) <- runStateT lowerHandler initial
  let instructions = reverse (codegenInstructions final)
      definition = unlines
        (["define internal ptr @vr_http_on_error(ptr %message) {", "entry:"]
          <> map ("  " <>) instructions
          <> ["  ret " <> typed page, "}", ""])
  pure (definition : reverse (codegenHelpers final))

lowerEndpointArgument :: ModuleContext -> Map.Map String Int64 -> NativeEndpoint -> M.Expr -> Int -> (M.Type, LlvmType) -> Codegen Operand
lowerEndpointArgument context _ _ source _ (sourceType, Ptr)
  | isOptionalQueryStringType sourceType = do
      queryString <- emitResult Ptr "call ptr @vr_runtime_current_query_string()"
      lowerMaybeString context source queryString
lowerEndpointArgument context _ endpoint source parameterIndex (sourceType, I8)
  | endpointPostOnly endpoint
  , Nothing <- endpointRpcResult endpoint
  , not (endpointExtern endpoint)
  , parameterIndex == length (endpointUrlArguments endpoint) = pure (Operand I8 "0")
  | null (endpointUrlArguments endpoint) = pure (Operand I8 "0")
  | [_] <- endpointUrlArguments endpoint, Nothing <- endpointRpcResult endpoint = pure (Operand I8 "0")
  | otherwise = lowerUrlDecodeNext context source Map.empty sourceType I8
lowerEndpointArgument _ _ _ _ _ (sourceType, Ptr)
  | M.TFfi "Basis" "postBody" <- locatedValue sourceType = pure (Operand Ptr "%request_context")
lowerEndpointArgument context inputSlots endpoint source parameterIndex (sourceType, typ@(Record fields))
  | Nothing <- endpointRpcResult endpoint
  , endpointPostOnly endpoint && not (endpointExtern endpoint)
  , parameterIndex == length (endpointUrlArguments endpoint) = case locatedValue sourceType of
      M.TRecord sourceFields
        | map fst sourceFields == map fst fields ->
            lowerIndexedFormRecord context inputSlots source sourceFields typ
      _ -> failCodegen source "llvm-form-record"
        "Native form argument descriptors do not match the handler record"
lowerEndpointArgument context _ endpoint source parameterIndex (sourceType, typ)
  | Just _ <- endpointRpcResult endpoint = do
      lowerUrlDecodeNext context source Map.empty sourceType typ
  | not (endpointPostOnly endpoint) || endpointExtern endpoint = do
      lowerUrlDecodeNext context source Map.empty sourceType typ
  | parameterIndex < length (endpointUrlArguments endpoint) = do
      lowerUrlDecodeNext context source Map.empty sourceType typ
  | otherwise = failCodegen source "llvm-http-arguments"
      ("Native HTTP argument decoding is not implemented for " <> renderType typ)

lowerIndexedFormRecord
  :: ModuleContext
  -> Map.Map String Int64
  -> M.Expr
  -> [(String, M.Type)]
  -> LlvmType
  -> Codegen Operand
lowerIndexedFormRecord context inputSlots source sourceFields resultType = case resultType of
  Record fields
    | map fst sourceFields == map fst fields ->
        foldM insert (Operand resultType "undef")
          (zip [0 :: Int ..] (zip sourceFields fields))
  _ -> failCodegen source "llvm-form-record"
    "Indexed form argument descriptors do not match the handler record"
  where
    insert aggregate (index, ((name, sourceType), (_, fieldType))) = do
      decoded <- lowerIndexedFormField
        context inputSlots source name sourceType fieldType
      emitResult resultType
        ("insertvalue " <> renderType resultType <> " " <> operandText aggregate
          <> ", " <> typed decoded <> ", " <> show index)

lowerIndexedFormField
  :: ModuleContext
  -> Map.Map String Int64
  -> M.Expr
  -> String
  -> M.Type
  -> LlvmType
  -> Codegen Operand
lowerIndexedFormField context inputSlots source name sourceType resultType = do
  slot <- case Map.lookup name inputSlots of
    Just found -> pure found
    Nothing -> failCodegen source "llvm-form-slot"
      ("No application input slot was allocated for field " <> name)
  case locatedValue sourceType of
    M.TRecord fields -> do
      emitInstruction
        ("call void @uw_enter_subform(ptr %request_context, i32 " <> show slot <> ")")
      result <- lowerIndexedFormRecord context inputSlots source fields resultType
      emitInstruction "call void @uw_leave_subform(ptr %request_context)"
      pure result
    M.TList element ->
      lowerIndexedFormList context inputSlots source slot element resultType
    M.TOption element ->
      lowerIndexedFormOption context inputSlots source slot element resultType
    M.TFfi "Basis" "file"
      | resultType == Ptr -> emitResult Ptr
          ("call ptr @vr_runtime_get_indexed_form_file(ptr %request_context, i64 "
            <> show slot <> ")")
    _ -> do
      let isBoolean = case locatedValue sourceType of
            M.TFfi "Basis" "bool" -> True
            _ -> False
          requiredName = if isBoolean
            then Operand Ptr "null"
            else stringOperand context (ByteString8.pack name)
      raw <- emitResult Ptr
        ("call ptr @vr_runtime_get_indexed_form_field(ptr %request_context, i64 "
          <> show slot <> ", " <> typed requiredName <> ", i1 "
          <> llvmBool isBoolean <> ")")
      lowerFormDecode context source sourceType resultType raw

lowerIndexedFormOption
  :: ModuleContext
  -> Map.Map String Int64
  -> M.Expr
  -> Int64
  -> M.Type
  -> LlvmType
  -> Codegen Operand
lowerIndexedFormOption context _ source slot element resultType = do
  ensureOperand source Ptr (Operand resultType "null")
  raw <- emitResult Ptr
    ("call ptr @vr_runtime_get_indexed_form_field(ptr %request_context, i64 "
      <> show slot <> ", ptr null, i1 false)")
  present <- emitResult I1 ("icmp ne ptr " <> operandText raw <> ", null")
  noneLabel <- freshLabel "form_none"
  someLabel <- freshLabel "form_some"
  mergeLabel <- freshLabel "form_option_merge"
  emitInstruction
    ("br i1 " <> operandText present <> ", label %" <> someLabel
      <> ", label %" <> noneLabel)
  emitBlock noneLabel
  none <- allocateTagged context source 0 Nothing
  noneBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock someLabel
  elementType <- liftEither (lowerTypeAt (locatedSpan source) element)
  payload <- lowerFormDecode context source element elementType raw
  some <- allocateTagged context source 1 (Just payload)
  someBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock mergeLabel
  emitResult Ptr
    ("phi ptr [ " <> operandText none <> ", %" <> noneBlock <> " ], [ "
      <> operandText some <> ", %" <> someBlock <> " ]")

lowerIndexedFormList
  :: ModuleContext
  -> Map.Map String Int64
  -> M.Expr
  -> Int64
  -> M.Type
  -> LlvmType
  -> Codegen Operand
lowerIndexedFormList context inputSlots source slot element resultType = do
  ensureOperand source Ptr (Operand resultType "null")
  elementType <- liftEither (lowerTypeAt (locatedSpan source) element)
  nil <- allocateTagged context source 0 Nothing
  resultAddress <- allocate Ptr
  statusAddress <- allocate I32
  emitInstruction ("store " <> typed nil <> ", ptr " <> operandText resultAddress)
  initialStatus <- emitResult I32
    ("call i32 @uw_enter_subforms(ptr %request_context, i32 " <> show slot <> ")")
  emitInstruction
    ("store " <> typed initialStatus <> ", ptr " <> operandText statusAddress)
  loopLabel <- freshLabel "form_list_loop"
  itemLabel <- freshLabel "form_list_item"
  doneLabel <- freshLabel "form_list_done"
  emitInstruction ("br label %" <> loopLabel)
  emitBlock loopLabel
  status <- emitResult I32 ("load i32, ptr " <> operandText statusAddress)
  hasItem <- emitResult I1 ("icmp ne i32 " <> operandText status <> ", 0")
  emitInstruction
    ("br i1 " <> operandText hasItem <> ", label %" <> itemLabel
      <> ", label %" <> doneLabel)
  emitBlock itemLabel
  value <- case locatedValue element of
    M.TRecord fields ->
      lowerIndexedFormRecord context inputSlots source fields elementType
    _ -> failCodegen source "llvm-form-list"
      "Nested form lists must contain record entries"
  rest <- emitResult Ptr ("load ptr, ptr " <> operandText resultAddress)
  payload <- buildRecordOperand source [("1", value), ("2", rest)]
  cons <- allocateTagged context source 1 (Just payload)
  emitInstruction ("store " <> typed cons <> ", ptr " <> operandText resultAddress)
  nextStatus <- emitResult I32 "call i32 @uw_next_entry(ptr %request_context)"
  emitInstruction
    ("store " <> typed nextStatus <> ", ptr " <> operandText statusAddress)
  emitInstruction ("br label %" <> loopLabel)
  emitBlock doneLabel
  emitResult Ptr ("load ptr, ptr " <> operandText resultAddress)

endpointHandlerArguments :: NativeEndpoint -> [M.Type]
endpointHandlerArguments endpoint = case endpointArguments endpoint of
  [] -> []
  arguments -> init arguments

-- Ur/Web treats the input table as a graph-coloring problem.  Fields in one
-- record are a clique because they coexist, while fields in distinct nested
-- records or unrelated actions may reuse a slot.  Names are colored in
-- lexical order with the smallest available nonnegative number.  Even an
-- application with no actions reports one slot: the upstream C printer uses
-- @max 0 colors + 1@.
allocateApplicationInputs :: [NativeEndpoint] -> (Map.Map String Int64, Int64)
allocateApplicationInputs endpoints = (colors, maximumColor + 1)
  where
    conflicts = foldl' addClique Map.empty (concatMap endpointInputCliques endpoints)
    colors = Map.foldlWithKey' colorName Map.empty conflicts
    maximumColor = Map.foldl' max 0 colors

    addClique known names = foldl' addName known (Set.toList members)
      where
        members = Set.fromList names
        addName graph name = Map.insertWith Set.union name
          (Set.delete name members) graph

    colorName assigned name neighbors = Map.insert name (firstAvailable 0) assigned
      where
        unavailable = Set.fromList
          [ color
          | neighbor <- Set.toList neighbors
          , Just color <- [Map.lookup neighbor assigned]
          ]
        firstAvailable candidate
          | Set.member candidate unavailable = firstAvailable (candidate + 1)
          | otherwise = candidate

endpointInputCliques :: NativeEndpoint -> [[String]]
endpointInputCliques endpoint
  | endpointPostOnly endpoint && not (endpointExtern endpoint) =
      case reverse (endpointHandlerArguments endpoint) of
        formType : _ -> typeInputCliques signatureNames formType
        [] -> []
  | otherwise = []
  where
    signatureNames = case endpointXsrfTransport endpoint of
      NativeXsrfForm field -> [ByteString8.unpack field]
      _ -> []

    typeInputCliques always typ = case locatedValue typ of
      M.TRecord fields ->
        (always <> map fst fields)
          : concatMap (typeInputCliques [] . snd) fields
      M.TList element -> typeInputCliques [] element
      _ -> []

endpointUrlArguments :: NativeEndpoint -> [M.Type]
endpointUrlArguments endpoint
  | Just _ <- endpointRpcResult endpoint = withoutQueryString (endpointHandlerArguments endpoint)
  | endpointExtern endpoint = filter (not . isImplicitExternType) (endpointHandlerArguments endpoint)
  | endpointPostOnly endpoint = initOrEmpty (endpointHandlerArguments endpoint)
  | otherwise = withoutQueryString (endpointHandlerArguments endpoint)
  where
    withoutQueryString = filter (not . isOptionalQueryStringType)
    initOrEmpty [] = []
    initOrEmpty values = init values
    isImplicitExternType typ = isPostBodyType typ || isOptionalQueryStringType typ
    isPostBodyType typ = case locatedValue typ of
      M.TFfi "Basis" "postBody" -> True
      _ -> False

isOptionalQueryStringType :: M.Type -> Bool
isOptionalQueryStringType typ = case locatedValue typ of
  M.TOption element -> case locatedValue element of
    M.TFfi "Basis" "queryString" -> True
    _ -> False
  _ -> False

lowerUrlDecode :: ModuleContext -> M.Expr -> M.Type -> LlvmType -> Operand -> Codegen Operand
lowerUrlDecode _ source sourceType resultType component = case locatedValue sourceType of
  M.TFfi "Basis" "int" -> call I64 "vr_runtime_unurlify_int"
  M.TFfi "Basis" "float" -> call F64 "vr_runtime_unurlify_float"
  M.TFfi "Basis" "bool" -> call I1 "vr_runtime_unurlify_bool"
  M.TFfi "Basis" "char" -> call I32 "vr_runtime_unurlify_char"
  M.TFfi "Basis" "time" -> call Ptr "vr_runtime_unurlify_time"
  M.TFfi "Basis" "channel" -> call Ptr "vr_runtime_channel_lookup"
  M.TFfi "Basis" _ -> call Ptr "vr_runtime_unurlify_string"
  _ -> failCodegen source "llvm-url-type" "Native URL parsing does not yet support this argument type"
  where
    call expected function
      | expected == resultType = emitResult expected ("call " <> renderType expected <> " @" <> function <> "(" <> typed component <> ")")
      | otherwise = failCodegen source "llvm-url-type" "URL decoder result does not match the handler argument"

-- Form fields have already been decoded from application/x-www-form-urlencoded
-- by the runtime.  They must not pass through Ur's distinct dot-escaped URL
-- component decoder a second time (ordinary input such as "a.b" would then be
-- misread as a malformed .HH escape).
lowerFormDecode :: ModuleContext -> M.Expr -> M.Type -> LlvmType -> Operand -> Codegen Operand
lowerFormDecode context source sourceType resultType value = case locatedValue sourceType of
  M.TFfi "Basis" "int" -> call I64 "vr_runtime_unurlify_int"
  M.TFfi "Basis" "float" -> call F64 "vr_runtime_unurlify_float"
  M.TFfi "Basis" "bool" -> call I1 "vr_runtime_unurlify_bool"
  M.TFfi "Basis" "char" -> call I32 "vr_runtime_form_char"
  M.TFfi "Basis" "file"
    | resultType == Ptr -> pure value
  M.TFfi "Basis" _
    | resultType == Ptr -> pure value
  M.TFfi moduleName typeName
    | Set.member (moduleName, typeName) (moduleForeignCodecs context) -> do
        ensureUrlResultType source Ptr resultType
        (decoded, consumed) <- lowerForeignCodecDecode context source moduleName typeName value
        emitInstruction
          ("call void @vr_runtime_require_consumed_components(" <> typed value <> ", "
            <> typed consumed <> ")")
        pure decoded
  _ -> failCodegen source "llvm-form-type" "Native form parsing does not yet support this field type"
  where
    call expected function
      | expected == resultType = emitResult expected
          ("call " <> renderType expected <> " @" <> function <> "(" <> typed value <> ")")
      | otherwise = failCodegen source "llvm-form-type" "Form decoder result does not match the handler field"

lowerUrlDecodeNext
  :: ModuleContext
  -> M.Expr
  -> Map.Map M.GlobalId String
  -> M.Type
  -> LlvmType
  -> Codegen Operand
lowerUrlDecodeNext context source =
  lowerComponentDecodeNext context source "vr_runtime_next_url_component"

lowerComponentDecodeNext
  :: ModuleContext
  -> M.Expr
  -> String
  -> Map.Map M.GlobalId String
  -> M.Type
  -> LlvmType
  -> Codegen Operand
lowerComponentDecodeNext context source componentFunction recursive sourceType resultType = case locatedValue sourceType of
  M.TRecord [] -> do
    component <- nextUrlComponent componentFunction
    emitInstruction
      ("call void @vr_runtime_expect_url_component(" <> typed component <> ", "
        <> typed (stringOperand context (ByteString8.pack "_")) <> ")")
    ensureUrlResultType source I8 resultType
    pure (Operand I8 "0")
  M.TRecord sourceFields -> case resultType of
    Record fields
      | map fst sourceFields == map fst fields ->
          foldM decodeField (Operand resultType "undef") (zip [0 :: Int ..] (zip sourceFields fields))
    _ -> failCodegen source "llvm-url-type" "URL record decoder result does not match the handler argument"
    where
      decodeField aggregate (index, ((_, fieldSourceType), (_, fieldType))) = do
        field <- lowerComponentDecodeNext context source componentFunction recursive fieldSourceType fieldType
        emitResult resultType
          ("insertvalue " <> renderType resultType <> " " <> operandText aggregate <> ", "
            <> typed field <> ", " <> show index)
  M.TOption element -> do
    ensureUrlResultType source Ptr resultType
    component <- nextUrlComponent componentFunction
    lowerUrlDecodeChoice context source component
      [ ("None", allocateTagged context source 0 Nothing)
      , ("Some", do
          elementType <- liftEither (lowerTypeAt (locatedSpan source) element)
          payload <- lowerComponentDecodeNext context source componentFunction recursive element elementType
          allocateTagged context source 1 (Just payload))
      ]
  M.TList element -> do
    ensureUrlResultType source Ptr resultType
    lowerListUrlDecoder context source componentFunction recursive sourceType element
  M.TDatatype identifier -> do
    ensureUrlResultType source Ptr resultType
    case Map.lookup identifier recursive of
      Just helper -> callUrlDecodeHelper helper
      Nothing -> lowerDatatypeUrlDecoder context source componentFunction recursive identifier
  M.TFfi moduleName typeName
    | Set.member (moduleName, typeName) (moduleForeignCodecs context) -> do
        ensureUrlResultType source Ptr resultType
        remaining <- case componentFunction of
          "vr_runtime_next_url_component" ->
            emitResult Ptr "call ptr @vr_runtime_remaining_url_components()"
          "vr_runtime_next_unurlify_component" ->
            emitResult Ptr "call ptr @vr_runtime_remaining_unurlify_components()"
          _ -> failCodegen source "llvm-url-codec" "Unknown URL component stream"
        (decoded, consumed) <- lowerForeignCodecDecode
          context source moduleName typeName remaining
        case componentFunction of
          "vr_runtime_next_url_component" ->
            emitInstruction ("call void @vr_runtime_consume_url_components(" <> typed consumed <> ")")
          "vr_runtime_next_unurlify_component" ->
            emitInstruction ("call void @vr_runtime_consume_unurlify_components(" <> typed consumed <> ")")
          _ -> pure ()
        pure decoded
  _ -> nextUrlComponent componentFunction >>= lowerUrlDecode context source sourceType resultType

lowerForeignCodecDecode
  :: ModuleContext -> M.Expr -> String -> String -> Operand -> Codegen (Operand, Operand)
lowerForeignCodecDecode _context source moduleName typeName encoded = do
  ensureOperand source Ptr encoded
  consumedAddress <- allocate I64
  runtimeContext <- emitResult Ptr "call ptr @vr_runtime_current_context()"
  decoded <- emitResult Ptr
    ("call ptr @" <> foreignCodecDecodeSymbol moduleName typeName <> "("
      <> typed runtimeContext <> ", " <> typed encoded <> ", " <> typed consumedAddress <> ")")
  consumed <- emitResult I64 ("load i64, ptr " <> operandText consumedAddress)
  pure (decoded, consumed)

nextUrlComponent :: String -> Codegen Operand
nextUrlComponent function = emitResult Ptr ("call ptr @" <> function <> "()")

ensureUrlResultType :: M.Expr -> LlvmType -> LlvmType -> Codegen ()
ensureUrlResultType source expected actual
  | expected == actual = pure ()
  | otherwise = failCodegen source "llvm-url-type" "URL decoder result does not match the handler argument"

lowerUrlDecodeChoice
  :: ModuleContext
  -> M.Expr
  -> Operand
  -> [(String, Codegen Operand)]
  -> Codegen Operand
lowerUrlDecodeChoice context source component alternatives = do
  testLabels <- mapM (const (freshLabel "url_decode_test")) alternatives
  bodyLabels <- mapM (const (freshLabel "url_decode_body")) alternatives
  failureLabel <- freshLabel "url_decode_failure"
  mergeLabel <- freshLabel "url_decode_merge"
  case testLabels of
    first : _ -> emitInstruction ("br label %" <> first)
    [] -> failCodegen source "llvm-url-type" "URL decoder has no alternatives"
  incoming <- forM (zip4 alternatives testLabels bodyLabels (drop 1 testLabels <> [failureLabel])) $
    \((name, action), testLabel, bodyLabel, nextLabel) -> do
      emitBlock testLabel
      comparison <- emitResult I32
        ("call i32 @strcmp(" <> typed component <> ", "
          <> typed (stringOperand context (ByteString8.pack name)) <> ")")
      matches <- emitResult I1 ("icmp eq i32 " <> operandText comparison <> ", 0")
      emitInstruction
        ("br i1 " <> operandText matches <> ", label %" <> bodyLabel <> ", label %" <> nextLabel)
      emitBlock bodyLabel
      value <- action
      predecessor <- gets codegenCurrentBlock
      emitInstruction ("br label %" <> mergeLabel)
      pure (value, predecessor)
  emitBlock failureLabel
  emitInstruction
    ("call void @vr_runtime_fail(" <> typed (stringOperand context (ByteString8.pack "Invalid URL encoding")) <> ")")
  emitInstruction "unreachable"
  emitBlock mergeLabel
  case incoming of
    [] -> failCodegen source "llvm-url-type" "URL decoder has no results"
    (first, _) : _ -> do
      forM_ incoming $ \(value, _) -> ensureOperand source (operandType first) value
      emitResult (operandType first)
        ("phi " <> renderType (operandType first) <> " " <> intercalate ", "
          ["[ " <> operandText value <> ", %" <> predecessor <> " ]" | (value, predecessor) <- incoming])

lowerListUrlDecoder
  :: ModuleContext
  -> M.Expr
  -> String
  -> Map.Map M.GlobalId String
  -> M.Type
  -> M.Type
  -> Codegen Operand
lowerListUrlDecoder context source componentFunction recursive listType element = do
  helper <- freshHelperName "url_decode_list"
  let initial = initialCodegenState helper []
      body = do
        component <- nextUrlComponent componentFunction
        lowerUrlDecodeChoice context source component
          [ ("Nil", allocateTagged context source 0 Nothing)
          , ("Cons", do
              elementType <- liftEither (lowerTypeAt (locatedSpan source) element)
              headValue <- lowerComponentDecodeNext context source componentFunction recursive element elementType
              tailValue <- callUrlDecodeHelper helper
              let payloadType = Located (locatedSpan source)
                    (M.TRecord [("1", element), ("2", listType)])
              payloadLlvm <- liftEither (lowerTypeAt (locatedSpan source) payloadType)
              payload <- case payloadLlvm of
                Record _ -> do
                  first <- emitResult payloadLlvm
                    ("insertvalue " <> renderType payloadLlvm <> " undef, " <> typed headValue <> ", 0")
                  emitResult payloadLlvm
                    ("insertvalue " <> renderType payloadLlvm <> " " <> operandText first <> ", "
                      <> typed tailValue <> ", 1")
                _ -> failCodegen source "llvm-url-type" "List URL payload is not a record"
              allocateTagged context source 1 (Just payload))
          ]
  (result, final) <- liftEither (runStateT body initial)
  addHelperDefinition helper I8 Ptr result final
  callUrlDecodeHelper helper

lowerDatatypeUrlDecoder
  :: ModuleContext
  -> M.Expr
  -> String
  -> Map.Map M.GlobalId String
  -> M.GlobalId
  -> Codegen Operand
lowerDatatypeUrlDecoder context source componentFunction recursive identifier = do
  datatypeInfo <- case Map.lookup identifier (moduleDatatypes context) of
    Just found -> pure found
    Nothing -> failCodegen source "llvm-url-type" "URL decoder refers to an unknown datatype"
  helper <- freshHelperName "url_decode_datatype"
  let recursive' = Map.insert identifier helper recursive
      initial = initialCodegenState helper []
      body = do
        component <- nextUrlComponent componentFunction
        lowerUrlDecodeChoice context source component
          [ (name, case payloadType of
              Nothing -> allocateTagged context source tag Nothing
              Just payloadSourceType -> do
                payloadType' <- liftEither (lowerTypeAt (locatedSpan source) payloadSourceType)
                payload <- lowerComponentDecodeNext context source componentFunction recursive' payloadSourceType payloadType'
                allocateTagged context source tag (Just payload))
          | (tag, (name, _, payloadType)) <- zip [0 :: Int ..] (datatypeConstructors datatypeInfo)
          ]
  (result, final) <- liftEither (runStateT body initial)
  addHelperDefinition helper I8 Ptr result final
  callUrlDecodeHelper helper

callUrlDecodeHelper :: String -> Codegen Operand
callUrlDecodeHelper helper = emitResult Ptr ("call ptr @" <> helper <> "(ptr null, i8 0)")

renderMain :: ModuleContext -> ByteString.ByteString -> ByteString.ByteString -> ByteString.ByteString -> Int64 -> Maybe Int64 -> [(ByteString.ByteString, Int64)] -> Int64 -> Map.Map String Int64 -> Int64 -> Maybe ByteString.ByteString -> [ByteString.ByteString] -> [ByteString.ByteString] -> Maybe ByteString.ByteString -> ByteString.ByteString -> Maybe ByteString.ByteString -> [ByteString.ByteString] -> [Int] -> [NativeFilter] -> [NativeTask] -> [NativeEndpoint] -> [ProjectAsset] -> Bool -> String
renderMain context timeFormat clientScript urlPrefix clientTimeout inputLimit resourceLimits minimumHeap inputSlots inputCount signatureFile xsrfCookies xsrfEnvironment fileCache databaseSystem database databaseInitializers schemaInitializers filters tasks endpoints assets hasOnError = unlines
  ( ["define i32 @main() {", "entry:"]
      <> ["  call void @vr_runtime_set_input_limit(i64 " <> show limit <> ")" | limit <- maybe [] pure inputLimit]
      <> [ "  call void @vr_runtime_set_limit(" <> typed (stringOperand context kind)
             <> ", i64 " <> show amount <> ")"
         | (kind, amount) <- resourceLimits
         ]
      <> ["  call void @vr_runtime_set_application_input_count(i64 " <> show inputCount <> ")"]
      <> [ "  call void @vr_runtime_add_application_input("
             <> typed (stringOperand context (ByteString8.pack name))
             <> ", i64 " <> show slot <> ")"
         | (name, slot) <- Map.toAscList inputSlots
         ]
      <> ["  call void @vr_runtime_set_min_heap(i64 " <> show minimumHeap <> ")"]
      <> ["  call void @vr_runtime_xsrf_set_sigfile(" <> typed (stringOperand context path) <> ")" | path <- maybe [] pure signatureFile]
      <> ["  call void @vr_runtime_xsrf_add_cookie(" <> typed (stringOperand context name) <> ")" | name <- xsrfCookies]
      <> ["  call void @vr_runtime_xsrf_add_environment(" <> typed (stringOperand context name) <> ")" | name <- xsrfEnvironment]
      <> ["  call void @vr_runtime_xsrf_initialize()"]
      <> ["  call void @vr_runtime_set_time_format(" <> typed (stringOperand context timeFormat) <> ")"]
      <> ["  call void @vr_runtime_http_set_client_script(" <> typed (stringOperand context clientScript) <> ")" | not (ByteString.null clientScript)]
      <> ["  call void @vr_runtime_http_set_url_prefix(" <> typed (stringOperand context urlPrefix) <> ")"]
      <> ["  call void @vr_runtime_clients_set_timeout(i64 " <> show clientTimeout <> ")"]
      <> ["  call void @vr_runtime_file_cache_configure(" <> typed (stringOperand context directory) <> ")" | directory <- maybe [] pure fileCache]
      -- Always give the runtime a chance to honor VR_DATABASE.  An empty
      -- compile-time connection remains a no-op, while this makes the native
      -- target consistent with the direct-JavaScript target for projects
      -- whose database is supplied only by the deployment environment.
      <> ["  call void @vr_runtime_database_configure(" <> typed (stringOperand context databaseSystem)
            <> ", " <> typed (stringOperand context (maybe ByteString.empty id database)) <> ")"]
      <> ["  call void @vr_runtime_database_initialize(" <> typed (stringOperand context command) <> ")" | command <- databaseInitializers]
      <> [ "  call void @vr_runtime_filter_add(" <> typed (stringOperand context (filterKind filter'))
             <> ", i1 " <> llvmBool (filterAllows filter')
             <> ", i1 " <> llvmBool (filterPrefix filter')
             <> ", " <> typed (stringOperand context (filterPattern filter')) <> ")"
         | filter' <- filters
         ]
      <> [ "  call void @vr_init_g" <> show (M.unGlobalId identifier) <> "()"
         | identifier <- moduleGlobalOrder context
         ]
      <> ["  call void @vr_runtime_http_set_error_handler(ptr @vr_http_on_error)" | hasOnError]
      <> ["  call void @vr_schema_" <> show index <> "()" | index <- schemaInitializers]
      <> ["  call void @vr_runtime_database_schema_done()"]
      <> concat
        [ case task of
            InitializeTask {} -> ["  call void @vr_task_" <> show index <> "(ptr null)"]
            ClientLeavesTask {} ->
              ["  call void @vr_runtime_client_leaves_add(ptr @vr_task_" <> show index <> ", ptr null)"]
            PeriodicTask seconds _ ->
              ["  call void @vr_runtime_periodic(i64 " <> show seconds <> ", ptr @vr_task_" <> show index <> ", ptr null)"]
        | (index, task) <- zip [0 :: Int ..] tasks
        ]
      <> [ "  call void @vr_runtime_http_add_route(" <> typed (stringOperand context (endpointUrl endpoint))
             <> ", i1 " <> llvmBool (endpointPostOnly endpoint)
             <> ", i1 " <> llvmBool (endpointHasPathArguments endpoint)
             <> ", i1 " <> llvmBool (case endpointRpcResult endpoint of Just _ -> True; Nothing -> False)
             <> ", i1 " <> llvmBool (endpointHasClient endpoint)
             <> ", i1 " <> llvmBool (endpointNeedsPush endpoint)
             <> ", i32 " <> show (endpointXsrfKind endpoint)
             <> ", " <> typed (stringOperand context (endpointXsrfField endpoint))
             <> ", i1 " <> llvmBool (endpointXsrfValidate endpoint)
             <> ", i1 " <> llvmBool (endpointPageNeedsSignature endpoint)
             <> ", ptr @vr_http_route_" <> show index <> ")"
         | (index, endpoint) <- zip [0 :: Int ..] endpoints
         ]
      <> [ "  call void @vr_runtime_http_add_asset(" <> typed (stringOperand context (projectAssetUri asset))
             <> ", " <> typed (stringOperand context (projectAssetMime asset))
             <> ", " <> typed (stringOperand context (projectAssetBytes asset))
             <> ", i64 " <> show (ByteString.length (projectAssetBytes asset)) <> ")"
         | asset <- assets
         ]
      -- The standalone Ur/Web protocol starts its HTTP service even for an
      -- application with no exported routes.  Such projects are useful as
      -- libraries and still compile to a runnable server that returns 404.
      <> ["  call void @vr_runtime_http_serve()", "  ret i32 0", "}"]
  )
  where
    endpointXsrfKind endpoint = case endpointXsrfTransport endpoint of
      NativeXsrfNone -> 0 :: Int
      NativeXsrfForm {} -> 1
      NativeXsrfRpc -> 2
    endpointXsrfField endpoint = case endpointXsrfTransport endpoint of
      NativeXsrfForm field -> field
      _ -> ByteString.empty

parseDatabaseSystem :: String -> DatabaseSystem
parseDatabaseSystem name = case map toLower name of
  "mysql" -> DatabaseMySQL
  "sqlite" -> DatabaseSQLite
  _ -> DatabasePostgres

databaseInitializationStrings :: DatabaseSystem -> Bool -> [M.Decl] -> [ByteString.ByteString]
databaseInitializationStrings database fileCache declarations = cacheCommands <> sequenceCommands
  where
    cacheCommands =
      [ ByteString8.pack "CREATE EXTENSION IF NOT EXISTS pgcrypto"
      | fileCache && database == DatabasePostgres
      ]
    sequenceCommands =
      [ ByteString8.pack (case database of
          DatabaseMySQL ->
            "CREATE TABLE IF NOT EXISTS vr_sequences (name VARCHAR(255) PRIMARY KEY, value BIGINT NOT NULL)"
          DatabasePostgres ->
            "CREATE TABLE IF NOT EXISTS vr_sequences (name TEXT PRIMARY KEY, value BIGINT NOT NULL)"
          DatabaseSQLite ->
            "CREATE TABLE IF NOT EXISTS vr_sequences (name TEXT PRIMARY KEY, value INTEGER NOT NULL)")
      | any isSequence declarations
      ]
    isSequence declaration = case locatedValue declaration of
      M.DSequence {} -> True
      _ -> False

schemaDeclarationStrings :: DatabaseSystem -> Bool -> M.Decl -> [ByteString.ByteString]
schemaDeclarationStrings database mangle declaration = case locatedValue declaration of
  M.DTable _ fields primary constraints ->
    let indexedFields = schemaIndexedFieldNames primary constraints
     in map (ByteString8.pack . sqlColumnDefinition database mangle indexedFields) fields
      <> map (ByteString8.pack . sqlIdentifier database . physicalColumnName mangle . fst) fields
      <> [ ByteString8.pack
            (sqlIdentifier database (physicalColumnName mangle name) <> "(255)")
         | (name, typ) <- fields
         , database == DatabaseMySQL
         , Set.member name indexedFields
         , sqlTextType typ
         ]
  M.DView _ fields _ ->
    map (ByteString8.pack . sqlIdentifier database . physicalColumnName mangle . fst) fields
  M.DIndex table modes -> maybe [] (pure . ByteString8.pack)
    (databaseIndexCommand database mangle table modes)
  _ -> []

databaseIndexCommand :: DatabaseSystem -> Bool -> String -> [(String, M.IndexMode)] -> Maybe String
databaseIndexCommand database mangle table modes
  | null columns = Nothing
  | otherwise = Just
      ("CREATE INDEX " <> ifNotExists <> sqlIdentifier database indexName
        <> " ON " <> sqlIdentifier database table <> accessMethod <> " ("
        <> intercalate ", " (map renderColumn columns) <> ")")
  where
    available (_, M.IndexSkipped) = False
    available (_, M.IndexTrigram) = database == DatabasePostgres
    available _ = True
    columns = filter available modes
    hasTrigram = any ((== M.IndexTrigram) . snd) columns
    ifNotExists = case database of
      DatabaseMySQL -> ""
      _ -> "IF NOT EXISTS "
    accessMethod = if database == DatabasePostgres && hasTrigram then " USING gist" else ""
    renderColumn (column, mode) =
      sqlIdentifier database (physicalColumnName mangle column) <> case (database, mode) of
        (DatabasePostgres, M.IndexTrigram) -> " gist_trgm_ops"
        _ -> ""
    indexName = table <> concatMap indexPart columns
    indexPart (column, mode) = '_' : physicalColumnName mangle column <> case mode of
      M.IndexTrigram -> "_trigram"
      _ -> ""

sqlColumnDefinition :: DatabaseSystem -> Bool -> Set.Set String -> (String, M.Type) -> String
sqlColumnDefinition database mangle indexedFields (field, typ) =
  sqlIdentifier database (physicalColumnName mangle field) <> " " <> columnType
    <> if nullableSqlType typ then "" else " NOT NULL"
    <> if database == DatabaseMySQL && sqlTimeType typ && not (nullableSqlType typ)
         then " DEFAULT CURRENT_TIMESTAMP"
         else ""
  where
    columnType
      | database == DatabaseMySQL
      , Set.member field indexedFields
      , sqlTextType typ = "VARCHAR(255)"
      | otherwise = sqlType database typ

sqlTextType :: M.Type -> Bool
sqlTextType typ = case locatedValue typ of
  M.TFfi "Basis" "string" -> True
  M.TOption element -> sqlTextType element
  _ -> False

schemaIndexedFieldNames :: M.Expr -> M.Expr -> Set.Set String
schemaIndexedFieldNames primary constraints = collect primary <> collect constraints
  where
    collect expression = case locatedValue expression of
      M.EFfi "Basis" intrinsic staticArguments
        | intrinsic `elem` ["primary_key", "unique", "foreign_key"] ->
            Set.fromList (schemaConstraintKeyNames intrinsic staticArguments)
      M.EFfiApp "Basis" intrinsic staticArguments arguments
        | intrinsic `elem` ["primary_key", "unique", "foreign_key"] ->
            Set.fromList (schemaConstraintKeyNames intrinsic staticArguments)
              <> foldMap (collect . fst) arguments
      M.EApp function argument -> collect function <> collect argument
      M.ERecord fields -> foldMap (collect . (\(_, value, _) -> value)) fields
      _ -> Set.empty

schemaConstraintKeyNames :: String -> [M.StaticArg] -> [String]
schemaConstraintKeyNames intrinsic arguments
  | intrinsic == "foreign_key" =
      take 1 [name | M.StaticName name <- arguments]
        <> [name | M.StaticRow fields <- arguments, (M.StaticName name, _) <- fields]
  | otherwise = schemaKeyNames arguments

physicalColumnName :: Bool -> String -> String
physicalColumnName mangle name = (if mangle then "uw_" else "") <> map toLower name

sqlColumnIdentifier :: ModuleContext -> String -> String
sqlColumnIdentifier context = sqlIdentifier (moduleDatabaseSystem context)
  . physicalColumnName (moduleMangleSql context)

sqlIdentifier :: DatabaseSystem -> String -> String
sqlIdentifier database value = delimiter : concatMap escape value <> [delimiter]
  where
    delimiter = case database of
      DatabaseMySQL -> '`'
      _ -> '"'
    escape character | character == delimiter = [delimiter, delimiter]
    escape character = [character]

sqlIdentifierVariants :: String -> [String]
sqlIdentifierVariants value = stableNub
  [ sqlIdentifier DatabasePostgres value
  , sqlIdentifier DatabaseMySQL value
  ]

nullableSqlType :: M.Type -> Bool
nullableSqlType typ = case locatedValue typ of
  M.TOption {} -> True
  _ -> False

sqlTimeType :: M.Type -> Bool
sqlTimeType typ = case locatedValue typ of
  M.TFfi "Basis" "time" -> True
  _ -> False

sqlType :: DatabaseSystem -> M.Type -> String
sqlType database typ = case locatedValue typ of
  M.TFfi "Basis" "int" -> choose "BIGINT" "BIGINT" "INTEGER"
  M.TFfi "Basis" "bool" -> choose "BOOLEAN" "BOOL" "INTEGER"
  M.TFfi "Basis" "time" -> choose "TIMESTAMP" "TIMESTAMP" "TEXT"
  M.TFfi "Basis" "float" -> choose "DOUBLE PRECISION" "DOUBLE" "REAL"
  M.TFfi "Basis" "blob" -> choose "BYTEA" "LONGBLOB" "BLOB"
  M.TFfi "Basis" "file" -> choose "BYTEA" "LONGBLOB" "BLOB"
  M.TFfi "Basis" "char" -> choose "CHARACTER" "CHAR" "TEXT"
  M.TFfi "Basis" "channel" -> choose "BIGINT" "BIGINT" "INTEGER"
  M.TFfi "Basis" "client" -> choose "INTEGER" "INT" "INTEGER"
  M.TOption element -> sqlType database element
  _ -> choose "TEXT" "LONGTEXT" "TEXT"
  where
    choose postgres mysql sqlite = case database of
      DatabasePostgres -> postgres
      DatabaseMySQL -> mysql
      DatabaseSQLite -> sqlite

endpointHasPathArguments :: NativeEndpoint -> Bool
endpointHasPathArguments endpoint =
  case endpointArguments endpoint of
  [] -> False
  _ -> case endpointUrlArguments endpoint of
    [] -> False
    [_] | Just _ <- endpointRpcResult endpoint -> True
    [only] -> not (isUnitType only)
    _ -> True

nativeFilters :: ProjectPlan -> [NativeFilter]
nativeFilters plan = map convert (projectFilterRules plan)
  where
    convert rule = NativeFilter
      (ByteString8.pack (kindName (filterRuleKind rule)))
      (filterRuleAction rule == FilterAllow)
      (filterRulePatternKind rule == PrefixPattern)
      (ByteString8.pack (filterRulePattern rule))
    kindName kind = case kind of
      FilterUrl -> "url"
      FilterMime -> "mime"
      FilterRequestHeader -> "requestHeader"
      FilterResponseHeader -> "responseHeader"
      FilterEnv -> "env"
      FilterMeta -> "meta"

llvmBool :: Bool -> String
llvmBool value = if value then "1" else "0"

nativeUrlPrefix :: [ProjectDirective] -> String
nativeUrlPrefix directives = normalize raw
  where
    configured =
      [ projectDirectiveArgument directive
      | directive <- directives
      , projectDirectiveName directive == "prefix"
      ]
    raw = case configured of
      [] -> "/"
      values -> last values
    normalize "" = "/"
    normalize value0
      | "http://" `prefixOf` value0 = normalize (originPath (drop 7 value0))
      | "https://" `prefixOf` value0 = normalize (originPath (drop 8 value0))
      where
        originPath value = case dropWhile (/= '/') value of
          "" -> "/"
          path -> path
    normalize value
      | last value == '/' = value
      | otherwise = value <> "/"
    prefixOf prefix value = take (length prefix) value == prefix

mountEndpoint :: String -> NativeEndpoint -> NativeEndpoint
mountEndpoint prefix endpoint
  | prefix == "/" = endpoint
  | otherwise = endpoint
      { endpointUrl = ByteString8.pack (init prefix <> ensureSlash (ByteString8.unpack (endpointUrl endpoint))) }
  where
    ensureSlash path = case path of
      '/' : _ -> path
      _ -> '/' : path

configureEndpointXsrf :: Set.Set ByteString.ByteString -> NativeEndpoint -> NativeEndpoint
configureEndpointXsrf exemptions endpoint = endpoint
  { endpointXsrfValidate = case endpointXsrfTransport endpoint of
      NativeXsrfNone -> False
      _ -> not (Set.member (endpointUrl endpoint) exemptions)
  }

mountAsset :: String -> ProjectAsset -> ProjectAsset
mountAsset prefix asset
  | prefix == "/" = asset
  | otherwise = asset
      { projectAssetUri = ByteString8.pack (init prefix <> ensureSlash (ByteString8.unpack (projectAssetUri asset))) }
  where
    ensureSlash path = case path of
      '/' : _ -> path
      _ -> '/' : path

stringOperand :: ModuleContext -> ByteString.ByteString -> Operand
stringOperand context bytes = case Map.lookup bytes (moduleStrings context) of
  Just (index, size) ->
    Operand Ptr ("getelementptr inbounds ([" <> show size <> " x i8], ptr @vr_str_" <> show index <> ", i64 0, i64 0)")
  Nothing -> Operand Ptr "null"

initialCodegenState :: String -> [Operand] -> CodegenState
initialCodegenState prefix locals = CodegenState
  { codegenNextRegister = 0
  , codegenInstructions = []
  , codegenLocals = locals
  , codegenCurrentBlock = "entry"
  , codegenHelperPrefix = prefix
  , codegenNextHelper = 0
  , codegenHelpers = []
  }

lowerExpr :: ModuleContext -> M.Expr -> Codegen Operand
lowerExpr context source = case locatedValue source of
  M.EPrim primitive -> lowerPrimitive context source primitive
  M.ERel index -> do
    locals <- gets codegenLocals
    case drop index locals of
      value : _ -> pure value
      [] -> failCodegen source "llvm-local" ("Invalid local index " <> show index)
  M.ECon _ (M.PConFfi "Basis" "bool" name _) Nothing
    | name == "True" -> pure (Operand I1 "1")
    | name == "False" -> pure (Operand I1 "0")
  M.ECon _ (M.PConFfi "Basis" "list" name payloadType) payload -> do
    payloadValue <- traverse (lowerExpr context) payload
    case (payloadType, payloadValue) of
      (Nothing, Nothing) -> allocateTagged context source (if name == "Nil" then 0 else 1) Nothing
      (Just declared, Just actual) -> do
        expected <- liftEither (lowerTypeAt (locatedSpan source) declared)
        ensureOperand source expected actual
        allocateTagged context source (if name == "Nil" then 0 else 1) (Just actual)
      _ -> failCodegen source "llvm-list-constructor" "List constructor payload does not match its declared type"
  M.ECon _ (M.PConFfi moduleName datatypeName name _) payload ->
    lowerForeignConstructor context source moduleName datatypeName name payload
  M.ECon _ (M.PConVar identifier) payload ->
    lowerConstructor context source identifier payload
  M.ENone elementType -> lowerOption context source 0 elementType Nothing
  M.ESome elementType value -> lowerOption context source 1 elementType (Just value)
  M.EApp {} ->
    let (function, arguments) = collectApplications source
     in applyDeferredAt context source function =<< mapM (lowerDeferred context) arguments
  M.EAbs name domain range body -> lowerLambdaClosure context source name domain range body
  M.EUnop operator value -> lowerUnaryOperator context source operator value
  M.EBinop _ operator left right -> lowerBinaryOperator context source operator left right
  M.ELet _ declaredType value body -> do
    expected <- liftEither (lowerTypeAt (locatedSpan source) declaredType)
    value' <- lowerExpected context expected value
    ensureOperand source expected value'
    withLocal value' (lowerExpr context body)
  M.ERecord [] -> pure (Operand I8 "0")
  M.ERecord fields -> lowerRecord context source fields
  M.EField record name -> lowerField context source record name
  M.ERecordConcat left right -> lowerRecordConcat context source left right
  M.ERecordCut record names -> lowerRecordCut context source record names
  M.ECase scrutinee branches _ resultType -> lowerCase context source scrutinee branches resultType
  M.EStrcat left right -> lowerStringConcat context source left right
  M.EError message typ -> lowerError context source message typ
  M.EReturnBlob content mimeType typ -> do
    blob <- case content of
      Just value -> lowerExpr context value
      Nothing -> emitResult Ptr "call ptr @vr_runtime_page_blob()"
    mime <- lowerExpr context mimeType
    ensureOperand source Ptr blob
    ensureOperand source Ptr mime
    emitInstruction ("call void @vr_runtime_return_blob(" <> typed blob <> ", " <> typed mime <> ")")
    resultType <- liftEither (lowerTypeAt (locatedSpan source) typ)
    pure (zeroOperand resultType)
  M.ERedirect value typ -> do
    url <- lowerExpr context value
    ensureOperand source Ptr url
    emitInstruction ("call void @vr_runtime_redirect(" <> typed url <> ")")
    resultType <- liftEither (lowerTypeAt (locatedSpan source) typ)
    pure (zeroOperand resultType)
  M.EWrite value | Just integer <- Server.integerHtmlArgument value -> do
    integer' <- lowerExpr context integer
    ensureOperand source I64 integer'
    emitInstruction ("call void @vr_runtime_write_int(" <> typed integer' <> ")")
    pure (Operand I8 "0")
  M.EWrite value | Just string <- Server.stringHtmlArgument value -> do
    string' <- lowerExpr context string
    ensureOperand source Ptr string'
    emitInstruction ("call void @vr_runtime_write_html(" <> typed string' <> ")")
    pure (Operand I8 "0")
  M.EWrite value -> do
    value' <- lowerExpr context value
    ensureOperand source Ptr value'
    emitInstruction ("call void @vr_runtime_write_page(" <> typed value' <> ")")
    pure (Operand I8 "0")
  M.ESeq first second -> lowerExpr context first >> lowerExpr context second
  M.EFfi moduleName name staticArguments -> lowerIntrinsic context source moduleName name staticArguments []
  M.EFfiApp moduleName name staticArguments arguments ->
    lowerIntrinsic context source moduleName name staticArguments
      [DeferredExpr expression | (expression, _) <- arguments]
  M.EStaticApp function argument -> case attachStaticArgument argument function of
    Just applied -> lowerExpr context applied
    Nothing -> failCodegen source "llvm-static-application"
      "Static application did not resolve to a native intrinsic"
  M.ERecv channel typ -> lowerReceive context source channel typ
  M.ESleep duration -> lowerSleep context source duration
  M.ESpawn action -> lowerSpawn context source action
  M.ESqlCache index typ keys action ->
    lowerSqlCache context source index typ keys action
  M.ESqlCacheFlush typ flushes action ->
    lowerSqlCacheFlush context source typ flushes action
  M.EUnurlify value typ optional -> lowerUnurlify context source value typ optional
  M.EJavaScript mode value -> lowerJavaScriptValue context source mode value
  M.ESignalSource value -> lowerExpr context value
  M.ENamed identifier -> case Map.lookup identifier (moduleFunctions context) of
    Just info -> lowerGlobalClosure context source info []
    Nothing -> lowerGlobalLoad context source identifier
  M.EClosure identifier captures -> case Map.lookup identifier (moduleFunctions context) of
    Just info -> mapM (lowerExpr context) captures >>= lowerGlobalClosure context source info
    Nothing -> failCodegen source "llvm-closure" ("Unknown closure function #" <> show (M.unGlobalId identifier))
  _ -> failCodegen source "llvm-expression" ("Unsupported Mono expression: " <> expressionTag (locatedValue source))

lowerUnurlify :: ModuleContext -> M.Expr -> M.Expr -> M.Type -> Bool -> Codegen Operand
lowerUnurlify context source value typ optional = do
  serialized <- lowerExpr context value
  ensureOperand source Ptr serialized
  resultType <- liftEither (lowerTypeAt (locatedSpan source) typ)
  let decode = do
        emitInstruction ("call void @vr_runtime_unurlify_begin(" <> typed serialized <> ")")
        decoded <- lowerComponentDecodeNext context source
          "vr_runtime_next_unurlify_component" Map.empty typ resultType
        emitInstruction "call void @vr_runtime_require_unurlify_done()"
        pure decoded
  if optional
    then do
      missing <- emitResult I1 ("icmp eq ptr " <> operandText serialized <> ", null")
      noneLabel <- freshLabel "unurlify_none"
      someLabel <- freshLabel "unurlify_some"
      mergeLabel <- freshLabel "unurlify_merge"
      emitInstruction ("br i1 " <> operandText missing <> ", label %" <> noneLabel <> ", label %" <> someLabel)
      emitBlock noneLabel
      none <- allocateTagged context source 0 Nothing
      noneBlock <- gets codegenCurrentBlock
      emitInstruction ("br label %" <> mergeLabel)
      emitBlock someLabel
      decoded <- decode
      some <- allocateTagged context source 1 (Just decoded)
      someBlock <- gets codegenCurrentBlock
      emitInstruction ("br label %" <> mergeLabel)
      emitBlock mergeLabel
      emitResult Ptr
        ("phi ptr [ " <> operandText none <> ", %" <> noneBlock <> " ], [ "
          <> operandText some <> ", %" <> someBlock <> " ]")
    else decode

lowerSqlCache
  :: ModuleContext
  -> M.Expr
  -> Int
  -> M.Type
  -> [M.Expr]
  -> M.Expr
  -> Codegen Operand
lowerSqlCache context source index sourceType keys action = do
  resultType <- liftEither (lowerTypeAt (locatedSpan source) sourceType)
  if bareSqlQuery action
    then makeScopedUnitClosure source "sql_cache" resultType (body resultType)
    else body resultType
  where
    body resultType = do
      keyValues <- mapM (lowerExpr context) keys
      mapM_ (ensureOperand source Ptr) keyValues
      keyArray <- lowerSqlCacheKeyArray source keyValues
      hit <- emitResult Ptr
        ("call ptr @vr_runtime_sql_cache_check(i64 " <> show index <> ", i64 "
          <> show (length keyValues) <> ", " <> typed keyArray <> ")")
      missed <- emitResult I1 ("icmp eq ptr " <> operandText hit <> ", null")
      missLabel <- freshLabel "sql_cache_miss"
      hitLabel <- freshLabel "sql_cache_hit"
      mergeLabel <- freshLabel "sql_cache_merge"
      emitInstruction
        ("br i1 " <> operandText missed <> ", label %" <> missLabel <> ", label %" <> hitLabel)
      emitBlock hitLabel
      emitInstruction ("call void @vr_runtime_unurlify_begin(" <> typed hit <> ")")
      hitValue <- lowerComponentDecodeNext context source
        "vr_runtime_next_unurlify_component" Map.empty sourceType resultType
      emitInstruction "call void @vr_runtime_require_unurlify_done()"
      hitBlock <- gets codegenCurrentBlock
      emitInstruction ("br label %" <> mergeLabel)
      emitBlock missLabel
      actionValue <- lowerExpr context action
      missValue <- runTransactionToType context source resultType actionValue
      if operandType missValue == resultType
        then pure ()
        else failCodegen source "llvm-sql-cache-action"
          ("SQL-cache miss body produced " <> renderType (operandType missValue)
            <> " instead of " <> renderType resultType)
      serialized <- lowerUrlEncode context source sourceType missValue
      emitInstruction
        ("call void @vr_runtime_sql_cache_store(i64 " <> show index <> ", i64 "
          <> show (length keyValues) <> ", " <> typed keyArray <> ", "
          <> typed serialized <> ")")
      missBlock <- gets codegenCurrentBlock
      emitInstruction ("br label %" <> mergeLabel)
      emitBlock mergeLabel
      ensureOperand source resultType hitValue
      if resultType == I8
        then pure (Operand I8 "0")
        else emitResult resultType
          ("phi " <> renderType resultType <> " [ " <> operandText hitValue <> ", %"
            <> hitBlock <> " ], [ " <> operandText missValue <> ", %" <> missBlock <> " ]")

bareSqlQuery :: M.Expr -> Bool
bareSqlQuery expression = case locatedValue expression of
  M.EQuery {} -> True
  _ -> case collectApplications expression of
    (headExpression, [_, _, _]) -> case locatedValue headExpression of
      M.EFfi "Basis" "query" _ -> True
      M.EFfiApp "Basis" "query" _ [] -> True
      _ -> False
    _ -> False

lowerSqlCacheFlush
  :: ModuleContext
  -> M.Expr
  -> M.Type
  -> [M.SqlCacheFlush]
  -> M.Expr
  -> Codegen Operand
lowerSqlCacheFlush context source sourceType flushes action = do
  resultType <- liftEither (lowerTypeAt (locatedSpan source) sourceType)
  makeScopedUnitClosure source "sql_cache_flush" resultType $ do
      mapM_ emitFlush flushes
      actionValue <- lowerExpr context action
      result <- runTransactionOperand context source actionValue
      ensureOperand source resultType result
      pure result
  where
    emitFlush flush = do
      keys <- mapM (maybe (pure (Operand Ptr "null")) (lowerExpr context))
        (M.sqlCacheFlushKeys flush)
      mapM_ (ensureOperand source Ptr) keys
      keyArray <- lowerSqlCacheKeyArray source keys
      emitInstruction
        ("call void @vr_runtime_sql_cache_flush(i64 "
          <> show (M.sqlCacheFlushIndex flush) <> ", i64 " <> show (length keys)
          <> ", " <> typed keyArray <> ")")

lowerSqlCacheKeyArray :: M.Expr -> [Operand] -> Codegen Operand
lowerSqlCacheKeyArray _ [] = pure (Operand Ptr "null")
lowerSqlCacheKeyArray source keys = do
  array <- emitResult Ptr ("alloca [" <> show (length keys) <> " x ptr]")
  forM_ (zip [0 :: Int ..] keys) $ \(index, key) -> do
    ensureOperand source Ptr key
    slot <- emitResult Ptr
      ("getelementptr inbounds [" <> show (length keys) <> " x ptr], ptr "
        <> operandText array <> ", i64 0, i64 " <> show index)
    emitInstruction ("store " <> typed key <> ", ptr " <> operandText slot)
  pure array

lowerJavaScriptValue
  :: ModuleContext
  -> M.Expr
  -> M.JavaScriptMode
  -> M.Expr
  -> Codegen Operand
lowerJavaScriptValue context source mode value = case mode of
  M.JavaScriptSource typ -> do
    value' <- lowerExpr context value
    lowerClientCapture context source typ value'
  M.JavaScriptAttribute -> failCodegen source "llvm-client-javascript"
    "Dynamic browser attributes require client-expression lowering"
  M.JavaScriptScript -> failCodegen source "llvm-client-javascript"
    "Dynamic browser scripts require client-expression lowering"

lowerForeignConstructor
  :: ModuleContext
  -> M.Expr
  -> String
  -> String
  -> String
  -> Maybe M.Expr
  -> Codegen Operand
lowerForeignConstructor context source moduleName datatypeName name payload = do
  constructor <- case Map.lookup (moduleName, datatypeName, name) (moduleForeignConstructors context) of
    Just found -> pure found
    Nothing -> failCodegen source "llvm-foreign-constructor"
      ("Unknown foreign constructor " <> moduleName <> "." <> datatypeName <> "." <> name)
  payloadPointer <- case (Server.foreignConstructorPayload constructor, payload) of
    (Nothing, Nothing) -> pure (Operand Ptr "null")
    (Just declared, Just expression) -> do
      expected <- liftEither (lowerTypeAt (locatedSpan source) declared)
      actual <- lowerExpr context expression
      ensureOperand source expected actual
      converted <- convertForeignArgument source declared actual
      case locatedValue declared of
        M.TFfi foreignModule _ | foreignModule /= "Basis" -> pure converted
        _ -> do
          allocation <- allocate (operandType converted)
          emitInstruction ("store " <> typed converted <> ", ptr " <> operandText allocation)
          pure allocation
    (Nothing, Just _) -> failCodegen source "llvm-foreign-constructor-payload"
      "A nullary foreign constructor received a payload"
    (Just _, Nothing) -> failCodegen source "llvm-foreign-constructor-payload"
      "A foreign constructor payload is missing"
  runtimeContext <- emitResult Ptr "call ptr @vr_runtime_current_context()"
  emitResult Ptr
    ("call ptr @vr_foreign_constructor_make_"
      <> show (Server.foreignConstructorId constructor) <> "("
      <> typed runtimeContext <> ", " <> typed payloadPointer <> ")")

lowerConstructor :: ModuleContext -> M.Expr -> M.GlobalId -> Maybe M.Expr -> Codegen Operand
lowerConstructor context source identifier payload = do
  info <- case Map.lookup identifier (moduleConstructors context) of
    Just found -> pure found
    Nothing -> failCodegen source "llvm-constructor" ("Unknown datatype constructor #" <> show (M.unGlobalId identifier))
  payloadValue <- traverse (lowerExpr context) payload
  case (constructorPayload info, payloadValue) of
    (Nothing, Nothing) -> allocateTagged context source (constructorTag info) Nothing
    (Just declared, Just actual) -> do
      expected <- liftEither (lowerTypeAt (locatedSpan source) declared)
      ensureOperand source expected actual
      allocateTagged context source (constructorTag info) (Just actual)
    (Nothing, Just _) -> failCodegen source "llvm-constructor-payload" "Nullary constructor received a payload"
    (Just _, Nothing) -> failCodegen source "llvm-constructor-payload" "Constructor payload is missing"

lowerOption :: ModuleContext -> M.Expr -> Int -> M.Type -> Maybe M.Expr -> Codegen Operand
lowerOption context source tag elementType payload = do
  payloadValue <- traverse (lowerExpr context) payload
  case payloadValue of
    Nothing -> allocateTagged context source tag Nothing
    Just actual -> do
      expected <- liftEither (lowerTypeAt (locatedSpan source) elementType)
      ensureOperand source expected actual
      allocateTagged context source tag (Just actual)

allocateTagged :: ModuleContext -> M.Expr -> Int -> Maybe Operand -> Codegen Operand
allocateTagged _ _ tag payload = do
  let header = Record [("tag", I32), ("payload", Ptr)]
  -- Keep the existing {tag, payload pointer} ABI, but give both parts one
  -- request-lifetime allocation. The payload starts after the header, which
  -- is aligned for every lowered payload type (at most pointer/i64/double).
  -- Add the original sizes rather than using a larger padded outer struct,
  -- so the number of bytes charged against the heap limit stays the same.
  object <- case payload of
    Nothing -> allocate header
    Just value -> emitResult Ptr
      ("call ptr @vr_runtime_alloc_value(i64 add (i64 " <> sizeOf header
        <> ", i64 " <> sizeOf (operandType value) <> "))")
  tagAddress <- emitResult Ptr ("getelementptr inbounds { i32, ptr }, ptr " <> operandText object <> ", i32 0, i32 0")
  emitInstruction ("store i32 " <> show tag <> ", ptr " <> operandText tagAddress)
  payloadAddress <- emitResult Ptr ("getelementptr inbounds { i32, ptr }, ptr " <> operandText object <> ", i32 0, i32 1")
  stored <- case payload of
    Nothing -> pure (Operand Ptr "null")
    Just value -> do
      allocation <- emitResult Ptr
        ("getelementptr { i32, ptr }, ptr " <> operandText object <> ", i32 1")
      emitInstruction ("store " <> typed value <> ", ptr " <> operandText allocation)
      pure allocation
  emitInstruction ("store ptr " <> operandText stored <> ", ptr " <> operandText payloadAddress)
  pure object

lowerRecord :: ModuleContext -> M.Expr -> [(M.StaticArg, M.Expr, M.Type)] -> Codegen Operand
lowerRecord context source fields = do
  described <- mapM describe fields
  let recordType = Record [(name, typ) | (name, typ, _) <- described]
  foldM (insert recordType) (Operand recordType "undef") (zip [0 :: Int ..] described)
  where
    describe (name, value, declared) = do
      fieldName <- staticName source name
      expected <- liftEither (lowerTypeAt (locatedSpan source) declared)
      actual <- lowerRecordValue context source fieldName value
      ensureOperand source expected actual
      pure (fieldName, expected, actual)
    insert recordType aggregate (index, (_, _, value)) =
      emitResult recordType
        ("insertvalue " <> renderType recordType <> " " <> operandText aggregate <> ", " <> typed value <> ", " <> show index)

lowerRecordValue :: ModuleContext -> M.Expr -> String -> M.Expr -> Codegen Operand
lowerRecordValue context source fieldName value
  | fieldName `elem` ["Action", "Link"] = lowerUrlValue context source value
  | otherwise = lowerExpr context value

lowerUrlValue :: ModuleContext -> M.Expr -> M.Expr -> Codegen Operand
lowerUrlValue context source expression = case locatedValue expression of
  M.EClosure identifier captures -> case (Map.lookup identifier (moduleUrls context), Map.lookup identifier (moduleUrlArguments context)) of
    (Just url, Just argumentTypes) -> do
      let typedCaptures = zip captures argumentTypes
      if isSingleUnitCapture typedCaptures
        then pure (stringOperand context url)
        else foldM appendCapture (stringOperand context url) typedCaptures
    _ -> failCodegen source "llvm-url" "Handler closure is not exported as a URL"
  M.ENamed identifier -> case Map.lookup identifier (moduleUrls context) of
    Just url -> pure (stringOperand context url)
    Nothing -> lowerExpr context expression
  _ -> lowerExpr context expression
  where
    appendCapture encoded (capture, typ)
      | isUnitType typ = appendComponent encoded (stringOperand context (ByteString8.pack "_"))
      | otherwise = do
          value <- lowerExpr context capture
          component <- lowerUrlEncode context source typ value
          appendComponent encoded component
    appendComponent encoded component = do
      withSlash <- lowerStringConcatOperands source encoded (stringOperand context (ByteString8.pack "/"))
      lowerStringConcatOperands source withSlash component
    isSingleUnitCapture [(_, typ)] = isUnitType typ
    isSingleUnitCapture _ = False

isUnitType :: M.Type -> Bool
isUnitType typ = case locatedValue typ of
  M.TRecord [] -> True
  M.TFfi "Basis" "unit" -> True
  _ -> False

lowerUrlEncode :: ModuleContext -> M.Expr -> M.Type -> Operand -> Codegen Operand
lowerUrlEncode context source = lowerUrlEncodeWith context source Map.empty

lowerUrlEncodeWith
  :: ModuleContext
  -> M.Expr
  -> Map.Map M.GlobalId String
  -> M.Type
  -> Operand
  -> Codegen Operand
lowerUrlEncodeWith context source recursive typ value = case locatedValue typ of
  M.TFfi "Basis" "int" -> call I64 "vr_runtime_urlify_int"
  M.TFfi "Basis" "float" -> call F64 "vr_runtime_urlify_float"
  M.TFfi "Basis" "bool" -> call I1 "vr_runtime_urlify_bool"
  M.TFfi "Basis" "char" -> call I32 "vr_runtime_urlify_char"
  M.TFfi "Basis" "time" -> call Ptr "vr_runtime_urlify_time"
  M.TFfi "Basis" "channel" -> call Ptr "vr_runtime_channel_id"
  M.TFfi "Basis" _ -> call Ptr "vr_runtime_urlify_string"
  M.TFfi moduleName typeName
    | Set.member (moduleName, typeName) (moduleForeignCodecs context) -> do
        ensureOperand source Ptr value
        runtimeContext <- emitResult Ptr "call ptr @vr_runtime_current_context()"
        emitResult Ptr
          ("call ptr @" <> foreignCodecEncodeSymbol moduleName typeName <> "("
            <> typed runtimeContext <> ", " <> typed value <> ")")
  M.TRecord [] -> pure (stringOperand context (ByteString8.pack "_"))
  M.TRecord sourceFields -> case operandType value of
    Record fields
      | map fst sourceFields == map fst fields -> do
          encoded <- forM (zip3 [0 :: Int ..] sourceFields fields) $
            \(index, (_, fieldSourceType), (_, fieldType)) -> do
              field <- emitResult fieldType
                ("extractvalue " <> renderType (operandType value) <> " " <> operandText value <> ", " <> show index)
              lowerUrlEncodeWith context source recursive fieldSourceType field
          joinUrlComponents context source encoded
    _ -> failCodegen source "llvm-url-type" "URL record encoder received a mismatched record value"
  M.TOption element -> do
    ensureOperand source Ptr value
    lowerTaggedUrlEncode context source value
      [ (0, pure (stringOperand context (ByteString8.pack "None")))
      , (1, do
          elementType <- liftEither (lowerTypeAt (locatedSpan source) element)
          payload <- loadTaggedExprPayload source value elementType
          encoded <- lowerUrlEncodeWith context source recursive element payload
          lowerStringConcatOperands source (stringOperand context (ByteString8.pack "Some/")) encoded)
      ]
  M.TList element -> do
    ensureOperand source Ptr value
    lowerListUrlEncoder context source recursive typ element value
  M.TDatatype identifier -> do
    ensureOperand source Ptr value
    case Map.lookup identifier recursive of
      Just helper -> callUrlEncodeHelper helper value
      Nothing -> lowerDatatypeUrlEncoder context source recursive identifier value
  _ -> failCodegen source "llvm-url-type" "Native URL generation does not yet support this argument type"
  where
    call expected function = do
      ensureOperand source expected value
      emitResult Ptr ("call ptr @" <> function <> "(" <> typed value <> ")")

joinUrlComponents :: ModuleContext -> M.Expr -> [Operand] -> Codegen Operand
joinUrlComponents context _ [] = pure (stringOperand context (ByteString8.pack "_"))
joinUrlComponents context source (first : rest) =
  foldM (appendUrlComponent context source) first rest

lowerTaggedUrlEncode
  :: ModuleContext
  -> M.Expr
  -> Operand
  -> [(Int, Codegen Operand)]
  -> Codegen Operand
lowerTaggedUrlEncode _context source value alternatives = do
  tagAddress <- emitResult Ptr
    ("getelementptr inbounds { i32, ptr }, ptr " <> operandText value <> ", i32 0, i32 0")
  tag <- emitResult I32 ("load i32, ptr " <> operandText tagAddress)
  testLabels <- mapM (const (freshLabel "url_encode_test")) alternatives
  bodyLabels <- mapM (const (freshLabel "url_encode_body")) alternatives
  failureLabel <- freshLabel "url_encode_failure"
  mergeLabel <- freshLabel "url_encode_merge"
  case testLabels of
    first : _ -> emitInstruction ("br label %" <> first)
    [] -> failCodegen source "llvm-url-type" "URL encoder has no alternatives"
  incoming <- forM (zip4 alternatives testLabels bodyLabels (drop 1 testLabels <> [failureLabel])) $
    \((expectedTag, action), testLabel, bodyLabel, nextLabel) -> do
      emitBlock testLabel
      matches <- emitResult I1
        ("icmp eq i32 " <> operandText tag <> ", " <> show expectedTag)
      emitInstruction
        ("br i1 " <> operandText matches <> ", label %" <> bodyLabel <> ", label %" <> nextLabel)
      emitBlock bodyLabel
      encoded <- action
      predecessor <- gets codegenCurrentBlock
      emitInstruction ("br label %" <> mergeLabel)
      pure (encoded, predecessor)
  emitBlock failureLabel
  emitInstruction "call void @llvm.trap()"
  emitInstruction "unreachable"
  emitBlock mergeLabel
  case incoming of
    [] -> failCodegen source "llvm-url-type" "URL encoder has no results"
    _ : _ -> do
      forM_ incoming $ \(encoded, _) -> ensureOperand source Ptr encoded
      emitResult Ptr
        ("phi ptr " <> intercalate ", "
          ["[ " <> operandText encoded <> ", %" <> predecessor <> " ]" | (encoded, predecessor) <- incoming])

loadTaggedExprPayload :: M.Expr -> Operand -> LlvmType -> Codegen Operand
loadTaggedExprPayload source value payloadType = do
  ensureOperand source Ptr value
  payloadField <- emitResult Ptr
    ("getelementptr inbounds { i32, ptr }, ptr " <> operandText value <> ", i32 0, i32 1")
  payloadAddress <- emitResult Ptr ("load ptr, ptr " <> operandText payloadField)
  emitResult payloadType ("load " <> renderType payloadType <> ", ptr " <> operandText payloadAddress)

lowerListUrlEncoder
  :: ModuleContext
  -> M.Expr
  -> Map.Map M.GlobalId String
  -> M.Type
  -> M.Type
  -> Operand
  -> Codegen Operand
lowerListUrlEncoder context source recursive listType element value = do
  helper <- freshHelperName "url_encode_list"
  let initial = initialCodegenState helper []
      body = do
        let argument = Operand Ptr "%argument"
            payloadSourceType = Located (locatedSpan source)
              (M.TRecord [("1", element), ("2", listType)])
        payloadType <- liftEither (lowerTypeAt (locatedSpan source) payloadSourceType)
        lowerTaggedUrlEncode context source argument
          [ (0, pure (stringOperand context (ByteString8.pack "Nil")))
          , (1, do
              payload <- loadTaggedExprPayload source argument payloadType
              case payloadType of
                Record [(_, headType), (_, tailType)] -> do
                  headValue <- emitResult headType
                    ("extractvalue " <> renderType payloadType <> " " <> operandText payload <> ", 0")
                  tailValue <- emitResult tailType
                    ("extractvalue " <> renderType payloadType <> " " <> operandText payload <> ", 1")
                  headEncoded <- lowerUrlEncodeWith context source recursive element headValue
                  tailEncoded <- callUrlEncodeHelper helper tailValue
                  pairEncoded <- appendUrlComponent context source headEncoded tailEncoded
                  lowerStringConcatOperands source
                    (stringOperand context (ByteString8.pack "Cons/")) pairEncoded
                _ -> failCodegen source "llvm-url-type" "List URL payload is not a two-field record")
          ]
  (result, final) <- liftEither (runStateT body initial)
  addHelperDefinition helper Ptr Ptr result final
  callUrlEncodeHelper helper value

lowerDatatypeUrlEncoder
  :: ModuleContext
  -> M.Expr
  -> Map.Map M.GlobalId String
  -> M.GlobalId
  -> Operand
  -> Codegen Operand
lowerDatatypeUrlEncoder context source recursive identifier value = do
  datatypeInfo <- case Map.lookup identifier (moduleDatatypes context) of
    Just found -> pure found
    Nothing -> failCodegen source "llvm-url-type" "URL encoder refers to an unknown datatype"
  helper <- freshHelperName "url_encode_datatype"
  let recursive' = Map.insert identifier helper recursive
      initial = initialCodegenState helper []
      body = do
        let argument = Operand Ptr "%argument"
        lowerTaggedUrlEncode context source argument
          [ (tag, case payloadSourceType of
              Nothing -> pure (stringOperand context (ByteString8.pack name))
              Just payloadType -> do
                payloadLlvm <- liftEither (lowerTypeAt (locatedSpan source) payloadType)
                payload <- loadTaggedExprPayload source argument payloadLlvm
                encoded <- lowerUrlEncodeWith context source recursive' payloadType payload
                lowerStringConcatOperands source
                  (stringOperand context (ByteString8.pack (name <> "/"))) encoded)
          | (tag, (name, _, payloadSourceType)) <- zip [0 :: Int ..] (datatypeConstructors datatypeInfo)
          ]
  (result, final) <- liftEither (runStateT body initial)
  addHelperDefinition helper Ptr Ptr result final
  callUrlEncodeHelper helper value

callUrlEncodeHelper :: String -> Operand -> Codegen Operand
callUrlEncodeHelper helper value =
  emitResult Ptr ("call ptr @" <> helper <> "(ptr null, " <> typed value <> ")")

appendUrlComponent :: ModuleContext -> M.Expr -> Operand -> Operand -> Codegen Operand
appendUrlComponent context source encoded component = do
  withSlash <- lowerStringConcatOperands source encoded
    (stringOperand context (ByteString8.pack "/"))
  lowerStringConcatOperands source withSlash component

lowerField :: ModuleContext -> M.Expr -> M.Expr -> M.StaticArg -> Codegen Operand
lowerField context source record name = do
  aggregate <- lowerExpr context record
  fieldName <- staticName source name
  case operandType aggregate of
    Record fields -> case lookupField fieldName fields of
      Just (index, typ) -> emitResult typ
        ("extractvalue " <> renderType (operandType aggregate) <> " " <> operandText aggregate <> ", " <> show index)
      Nothing -> failCodegen source "llvm-record-field" ("Record has no field named " <> fieldName)
    actual -> failCodegen source "llvm-record" ("Field projection received " <> renderType actual)

lowerRecordConcat :: ModuleContext -> M.Expr -> M.Expr -> M.Expr -> Codegen Operand
lowerRecordConcat context source left right = do
  left' <- lowerExpr context left
  right' <- lowerExpr context right
  case (operandType left', operandType right') of
    (I8, I8) -> pure (Operand I8 "0")
    (I8, Record {}) -> pure right'
    (Record {}, I8) -> pure left'
    (Record leftFields, Record rightFields) -> do
      let resultType = Record (leftFields <> rightFields)
      afterLeft <- copyRecordFields resultType 0 left' (Operand resultType "undef")
      copyRecordFields resultType (length leftFields) right' afterLeft
    _ -> failCodegen source "llvm-record-concat" "Record concatenation received a non-record operand"

lowerRecordCut :: ModuleContext -> M.Expr -> M.Expr -> [M.StaticArg] -> Codegen Operand
lowerRecordCut context source record removed = do
  aggregate <- lowerExpr context record
  names <- mapM (staticName source) removed
  case operandType aggregate of
    Record fields -> do
      let retained = [(index, field) | (index, field@(name, _)) <- zip [0 :: Int ..] fields, name `notElem` names]
      case retained of
        [] -> pure (Operand I8 "0")
        _ -> do
          let resultType = Record (map snd retained)
          foldM (copyOne resultType aggregate) (Operand resultType "undef") (zip [0 :: Int ..] retained)
    I8 -> pure (Operand I8 "0")
    _ -> failCodegen source "llvm-record-cut" "Record cut received a non-record operand"
  where
    copyOne resultType aggregate destination (destinationIndex, (sourceIndex, (_, typ))) = do
      value <- emitResult typ
        ("extractvalue " <> renderType (operandType aggregate) <> " " <> operandText aggregate <> ", " <> show sourceIndex)
      emitResult resultType
        ("insertvalue " <> renderType resultType <> " " <> operandText destination <> ", " <> typed value <> ", " <> show destinationIndex)

copyRecordFields :: LlvmType -> Int -> Operand -> Operand -> Codegen Operand
copyRecordFields resultType offset source initial = case operandType source of
  Record fields -> foldM copy initial (zip [0 :: Int ..] fields)
  _ -> pure initial
  where
    copy aggregate (index, (_, typ)) = do
      value <- emitResult typ
        ("extractvalue " <> renderType (operandType source) <> " " <> operandText source <> ", " <> show index)
      emitResult resultType
        ("insertvalue " <> renderType resultType <> " " <> operandText aggregate <> ", " <> typed value <> ", " <> show (offset + index))

lookupField :: String -> [(String, LlvmType)] -> Maybe (Int, LlvmType)
lookupField wanted fields = case [(index, typ) | (index, (name, typ)) <- zip [0 :: Int ..] fields, name == wanted] of
  result : _ -> Just result
  [] -> Nothing

staticName :: M.Expr -> M.StaticArg -> Codegen String
staticName _ (M.StaticName name) = pure name
staticName source _ = failCodegen source "llvm-static-name" "Record operation requires a resolved static field name"

lowerCase :: ModuleContext -> M.Expr -> M.Expr -> [(M.Pattern, M.Expr)] -> M.Type -> Codegen Operand
lowerCase context source scrutinee branches declaredResult = case branches of
  [] -> failCodegen source "llvm-empty-case" "A case expression has no branches"
  _ -> do
    expectedResult <- liftEither (lowerTypeAt (locatedSpan source) declaredResult)
    value <- lowerExpr context scrutinee
    testLabels <- mapM (const (freshLabel "case_test")) branches
    bodyLabels <- mapM (const (freshLabel "case_body")) branches
    failureLabel <- freshLabel "case_failure"
    mergeLabel <- freshLabel "case_merge"
    firstTest <- case testLabels of
      label : _ -> pure label
      [] -> failCodegen source "llvm-empty-case" "Internal case lowering produced no test block"
    emitInstruction ("br label %" <> firstTest)
    incoming <- forM (zip4 branches testLabels bodyLabels (drop 1 testLabels <> [failureLabel])) $
      \((pattern', body), testLabel, bodyLabel, nextLabel) -> do
        emitBlock testLabel
        condition <- patternCondition context value pattern'
        emitInstruction
          ("br i1 " <> operandText condition <> ", label %" <> bodyLabel <> ", label %" <> nextLabel)
        emitBlock bodyLabel
        bindings <- patternBindings context value pattern'
        result <- withPatternLocals bindings (lowerExpected context expectedResult body)
        predecessor <- gets codegenCurrentBlock
        emitInstruction ("br label %" <> mergeLabel)
        pure (result, predecessor)
    emitBlock failureLabel
    emitInstruction "call void @llvm.trap()"
    emitInstruction "unreachable"
    emitBlock mergeLabel
    case incoming of
      _ : _ -> pure ()
      [] -> failCodegen source "llvm-empty-case" "Internal case lowering produced no result"
    forM_ incoming $ \(actual, _) -> ensureOperand source expectedResult actual
    emitResult expectedResult
      ("phi " <> renderType expectedResult <> " " <> intercalate ", "
        ["[ " <> operandText actual <> ", %" <> predecessor <> " ]" | (actual, predecessor) <- incoming])

patternCondition :: ModuleContext -> Operand -> M.Pattern -> Codegen Operand
patternCondition context value pattern' = case locatedValue pattern' of
  M.PVar {} -> pure (Operand I1 "1")
  M.PPrim primitive -> do
    literal <- primitiveOperand context (locatedSpan pattern') primitive
    ensureSameLocated pattern' value literal
    case operandType value of
      Ptr -> do
        comparison <- emitResult I32 ("call i32 @strcmp(" <> typed value <> ", " <> typed literal <> ")")
        emitResult I1 ("icmp eq i32 " <> operandText comparison <> ", 0")
      F64 -> emitResult I1 ("fcmp oeq double " <> operandText value <> ", " <> operandText literal)
      typ -> emitResult I1
        ("icmp eq " <> renderType typ <> " " <> operandText value <> ", " <> operandText literal)
  M.PCon _ (M.PConFfi "Basis" "bool" name _) Nothing -> do
    ensurePatternType pattern' I1 value
    let expected = if name == "True" then "1" else "0"
    emitResult I1 ("icmp eq i1 " <> operandText value <> ", " <> expected)
  M.PCon _ (M.PConVar identifier) nested -> do
    info <- case Map.lookup identifier (moduleConstructors context) of
      Just found -> pure found
      Nothing -> failCodegen pattern' "llvm-pattern-constructor"
        ("Unknown pattern constructor #" <> show (M.unGlobalId identifier))
    outer <- taggedCondition pattern' value (constructorTag info)
    case nested of
      Nothing -> pure outer
      Just payloadPattern -> case constructorPayload info of
        Just payloadType -> do
          lowered <- liftEither (lowerTypeAt (locatedSpan pattern') payloadType)
          nestedPayloadCondition context pattern' value outer lowered payloadPattern
        Nothing -> failCodegen pattern' "llvm-pattern-payload"
          "Nullary constructor pattern has a payload"
  M.PCon _ (M.PConFfi "Basis" "list" name payloadType) nested -> do
    outer <- taggedCondition pattern' value (if name == "Nil" then 0 else 1)
    case nested of
      Nothing -> pure outer
      Just payloadPattern -> case payloadType of
        Just typ -> do
          lowered <- liftEither (lowerTypeAt (locatedSpan pattern') typ)
          nestedPayloadCondition context pattern' value outer lowered payloadPattern
        _ -> failCodegen pattern' "llvm-pattern-payload"
          "List constructor pattern payload does not match its type"
  M.PCon _ (M.PConFfi moduleName datatypeName name _) _ -> do
    constructor <- lookupForeignPatternConstructor context pattern' moduleName datatypeName name
    ensurePatternType pattern' Ptr value
    result <- emitResult I32
      ("call i32 @vr_foreign_constructor_match_"
        <> show (Server.foreignConstructorId constructor) <> "(" <> typed value <> ")")
    emitResult I1 ("icmp ne i32 " <> operandText result <> ", 0")
  M.PRecord fields -> do
    conditions <- forM fields $ \(name, nested, _) -> do
      field <- extractRecordField pattern' value name
      patternCondition context field nested
    combineConditions conditions
  M.PNone _ -> taggedCondition pattern' value 0
  M.PSome elementType nested -> do
    outer <- taggedCondition pattern' value 1
    lowered <- liftEither (lowerTypeAt (locatedSpan pattern') elementType)
    nestedPayloadCondition context pattern' value outer lowered nested

patternBindings :: ModuleContext -> Operand -> M.Pattern -> Codegen [Operand]
patternBindings context value pattern' = case locatedValue pattern' of
  M.PVar _ typ -> do
    expected <- liftEither (lowerTypeAt (locatedSpan pattern') typ)
    ensurePatternType pattern' expected value
    pure [value]
  M.PPrim {} -> pure []
  M.PCon _ (M.PConVar identifier) nested -> case nested of
    Nothing -> pure []
    Just payloadPattern -> do
      info <- case Map.lookup identifier (moduleConstructors context) of
        Just found -> pure found
        Nothing -> failCodegen pattern' "llvm-pattern-constructor"
          ("Unknown pattern constructor #" <> show (M.unGlobalId identifier))
      payloadType <- case constructorPayload info of
        Just typ -> liftEither (lowerTypeAt (locatedSpan pattern') typ)
        Nothing -> failCodegen pattern' "llvm-pattern-payload" "Nullary constructor pattern has a payload"
      payload <- loadTaggedPayload pattern' value payloadType
      patternBindings context payload payloadPattern
  M.PCon _ (M.PConFfi "Basis" "bool" _ _) _ -> pure []
  M.PCon _ (M.PConFfi "Basis" "list" _ payloadType) nested -> case (payloadType, nested) of
    (Nothing, Nothing) -> pure []
    (Just typ, Just payloadPattern) -> do
      lowered <- liftEither (lowerTypeAt (locatedSpan pattern') typ)
      payload <- loadTaggedPayload pattern' value lowered
      patternBindings context payload payloadPattern
    _ -> failCodegen pattern' "llvm-pattern-payload" "List constructor pattern payload does not match its type"
  M.PCon _ (M.PConFfi moduleName datatypeName name _) nested -> case nested of
    Nothing -> pure []
    Just payloadPattern -> do
      constructor <- lookupForeignPatternConstructor context pattern' moduleName datatypeName name
      payload <- lowerForeignConstructorPayload context pattern' value constructor
      patternBindings context payload payloadPattern
  M.PRecord fields -> fmap concat $ forM fields $ \(name, nested, _) -> do
    field <- extractRecordField pattern' value name
    patternBindings context field nested
  M.PNone _ -> pure []
  M.PSome elementType nested -> do
    typ <- liftEither (lowerTypeAt (locatedSpan pattern') elementType)
    payload <- loadTaggedPayload pattern' value typ
    patternBindings context payload nested

lookupForeignPatternConstructor
  :: ModuleContext
  -> M.Pattern
  -> String
  -> String
  -> String
  -> Codegen Server.ForeignConstructor
lookupForeignPatternConstructor context source moduleName datatypeName name =
  case Map.lookup (moduleName, datatypeName, name) (moduleForeignConstructors context) of
    Just constructor -> pure constructor
    Nothing -> failCodegen source "llvm-pattern-constructor"
      ("Unknown foreign constructor " <> moduleName <> "." <> datatypeName <> "." <> name)

lowerForeignConstructorPayload
  :: ModuleContext
  -> M.Pattern
  -> Operand
  -> Server.ForeignConstructor
  -> Codegen Operand
lowerForeignConstructorPayload _context source value constructor = do
  payloadType <- case Server.foreignConstructorPayload constructor of
    Just typ -> pure typ
    Nothing -> failCodegen source "llvm-pattern-payload"
      "A nullary foreign constructor pattern has a payload"
  ensurePatternType source Ptr value
  runtimeContext <- emitResult Ptr "call ptr @vr_runtime_current_context()"
  box <- emitResult Ptr
    ("call ptr @vr_foreign_constructor_payload_"
      <> show (Server.foreignConstructorId constructor) <> "("
      <> typed runtimeContext <> ", " <> typed value <> ")")
  expected <- liftEither (lowerTypeAt (locatedSpan source) payloadType)
  case locatedValue payloadType of
    M.TFfi moduleName _ | moduleName /= "Basis" -> do
      ensureOperand source expected box
      pure box
    _ -> do
      abiType <- liftEither (foreignSourceAbiType (locatedSpan source) payloadType)
      raw <- emitResult abiType
        ("load " <> renderType abiType <> ", ptr " <> operandText box)
      convertForeignResult source payloadType expected raw

taggedCondition :: M.Pattern -> Operand -> Int -> Codegen Operand
taggedCondition source value expected = do
  ensurePatternType source Ptr value
  tagAddress <- emitResult Ptr
    ("getelementptr inbounds { i32, ptr }, ptr " <> operandText value <> ", i32 0, i32 0")
  tag <- emitResult I32 ("load i32, ptr " <> operandText tagAddress)
  emitResult I1 ("icmp eq i32 " <> operandText tag <> ", " <> show expected)

nestedPayloadCondition
  :: ModuleContext -> M.Pattern -> Operand -> Operand -> LlvmType -> M.Pattern -> Codegen Operand
nestedPayloadCondition context source tagged outer payloadType nested = do
  nestedLabel <- freshLabel "pattern_payload"
  falseLabel <- freshLabel "pattern_outer_mismatch"
  mergeLabel <- freshLabel "pattern_nested_merge"
  emitInstruction
    ("br i1 " <> operandText outer <> ", label %" <> nestedLabel <> ", label %" <> falseLabel)
  emitBlock nestedLabel
  payload <- loadTaggedPayload source tagged payloadType
  nestedResult <- patternCondition context payload nested
  nestedBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock falseLabel
  falseBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock mergeLabel
  emitResult I1
    ("phi i1 [ " <> operandText nestedResult <> ", %" <> nestedBlock
      <> " ], [ 0, %" <> falseBlock <> " ]")

loadTaggedPayload :: M.Pattern -> Operand -> LlvmType -> Codegen Operand
loadTaggedPayload source value typ = do
  ensurePatternType source Ptr value
  fieldAddress <- emitResult Ptr
    ("getelementptr inbounds { i32, ptr }, ptr " <> operandText value <> ", i32 0, i32 1")
  payloadAddress <- emitResult Ptr ("load ptr, ptr " <> operandText fieldAddress)
  emitResult typ ("load " <> renderType typ <> ", ptr " <> operandText payloadAddress)

extractRecordField :: M.Pattern -> Operand -> String -> Codegen Operand
extractRecordField source aggregate name = case operandType aggregate of
  Record fields -> case lookupField name fields of
    Just (index, typ) -> emitResult typ
      ("extractvalue " <> renderType (operandType aggregate) <> " " <> operandText aggregate <> ", " <> show index)
    Nothing -> failCodegen source "llvm-record-pattern" ("Record pattern refers to absent field " <> name)
  actual -> failCodegen source "llvm-record-pattern" ("Record pattern received " <> renderType actual)

combineConditions :: [Operand] -> Codegen Operand
combineConditions [] = pure (Operand I1 "1")
combineConditions (first : rest) = foldM combine first rest
  where
    combine left right = emitResult I1 ("and i1 " <> operandText left <> ", " <> operandText right)

withPatternLocals :: [Operand] -> Codegen value -> Codegen value
withPatternLocals bindings action = do
  original <- gets codegenLocals
  modify' (\state -> state {codegenLocals = reverse bindings <> original})
  result <- action
  modify' (\state -> state {codegenLocals = original})
  pure result

ensurePatternType :: M.Pattern -> LlvmType -> Operand -> Codegen ()
ensurePatternType source expected actual
  | expected == operandType actual = pure ()
  | otherwise = failCodegen source "llvm-pattern-type"
      ("Pattern expected " <> renderType expected <> " but received " <> renderType (operandType actual))

ensureSameLocated :: Located value -> Operand -> Operand -> Codegen ()
ensureSameLocated source left right
  | operandType left == operandType right = pure ()
  | otherwise = failCodegen source "llvm-pattern-type" "Pattern literal and scrutinee have different LLVM types"

-- Intrinsics such as transaction_bind and numeric operations decide which
-- operands are evidence and which must be evaluated.  Preserve source
-- expressions until that decision rather than eagerly lowering dictionaries.
data Deferred = DeferredExpr M.Expr | Lowered Operand

lowerDeferred :: ModuleContext -> M.Expr -> Codegen Deferred
lowerDeferred _ = pure . DeferredExpr

force :: ModuleContext -> Deferred -> Codegen Operand
force context deferred = case deferred of
  DeferredExpr expression -> lowerExpr context expression
  Lowered value -> pure value

applyValue :: ModuleContext -> M.Expr -> [Operand] -> Codegen Operand
applyValue context function arguments = applyDeferred context function (map Lowered arguments)

applyDeferred :: ModuleContext -> M.Expr -> [Deferred] -> Codegen Operand
applyDeferred context function = applyDeferredAt context function function

applyDeferredAt :: ModuleContext -> M.Expr -> M.Expr -> [Deferred] -> Codegen Operand
applyDeferredAt context callSite function arguments = case locatedValue function of
  M.EFfi "Basis" name staticArguments
    | Just arity <- basisTransactionArity name
    , length arguments == arity + 1 -> do
        transaction <- lowerIntrinsic context callSite "Basis" name staticArguments
          (take arity arguments)
        case operandType transaction of
          Function I8 _ -> applyClosure context callSite transaction (last arguments)
          _ -> pure transaction
  M.EFfi moduleName name staticArguments ->
    lowerIntrinsic context callSite moduleName name staticArguments arguments
  M.EStaticApp nested staticArgument -> case attachStaticArgument staticArgument nested of
    Just applied ->
      let (headExpression, embeddedArguments) = collectApplications applied
       in applyDeferredAt context callSite headExpression
            (map DeferredExpr embeddedArguments <> arguments)
    Nothing -> failCodegen callSite "llvm-static-application"
      "Static application did not resolve to a native intrinsic"
  M.ENamed identifier -> case Map.lookup identifier (moduleFunctions context) of
    Just _ -> lowerGlobalCall context callSite identifier arguments
    Nothing -> do
      value <- lowerGlobalLoad context callSite identifier
      foldM (applyClosure context callSite) value arguments
  M.EAbs _ domain range body -> case arguments of
    [] -> lowerExpr context function
    first : rest -> do
      expected <- liftEither (lowerTypeAt (locatedSpan function) domain)
      resultType <- liftEither (lowerTypeAt (locatedSpan function) range)
      actual <- forceExpected context expected first
      result <- withLocal actual (lowerExpected context resultType body)
      foldM (applyClosure context callSite) result rest
  _ -> do
    closure <- lowerExpr context function
    foldM (applyClosure context callSite) closure arguments

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

attachStaticArgument :: M.StaticArg -> M.Expr -> Maybe M.Expr
attachStaticArgument argument expression = case locatedValue expression of
  M.EFfi moduleName name arguments ->
    Just (Located (locatedSpan expression) (M.EFfi moduleName name (arguments <> [argument])))
  M.EFfiApp moduleName name arguments values ->
    Just (Located (locatedSpan expression) (M.EFfiApp moduleName name (arguments <> [argument]) values))
  M.EApp function value -> do
    function' <- attachStaticArgument argument function
    pure (Located (locatedSpan expression) (M.EApp function' value))
  M.EStaticApp function existing -> do
    function' <- attachStaticArgument existing function
    attachStaticArgument argument function'
  _ -> Nothing

lowerGlobalLoad :: ModuleContext -> M.Expr -> M.GlobalId -> Codegen Operand
lowerGlobalLoad context source identifier = case Map.lookup identifier (moduleGlobals context) of
  Just info -> emitResult (globalType info)
    ("load " <> renderType (globalType info) <> ", ptr " <> globalName info)
  Nothing -> failCodegen source "llvm-global" ("Unknown global #" <> show (M.unGlobalId identifier))

lowerGlobalCall :: ModuleContext -> M.Expr -> M.GlobalId -> [Deferred] -> Codegen Operand
lowerGlobalCall context source identifier deferred = do
  info <- case Map.lookup identifier (moduleFunctions context) of
    Just found -> pure found
    Nothing -> failCodegen source "llvm-global" ("Unknown function global #" <> show (M.unGlobalId identifier))
  let arity = length (functionParameters info)
  arguments <- sequence
    [ forceExpected context expected argument
    | (argument, (_, expected)) <- zip (take arity deferred) (functionParameters info)
    ]
  if length arguments < arity
    then lowerGlobalClosure context source info arguments
    else do
      result <- emitResult (functionResult info) ("call " <> renderType (functionResult info) <> " " <> functionName info <> "(" <> intercalate ", " (map typed arguments) <> ")")
      foldM (applyClosure context source) result (drop arity deferred)

applyClosure :: ModuleContext -> M.Expr -> Operand -> Deferred -> Codegen Operand
applyClosure context source closure argument = case operandType closure of
  Function domain range -> do
    actual <- forceExpected context domain argument
    codeAddress <- emitResult Ptr
      ("getelementptr inbounds { ptr, ptr, ptr }, ptr " <> operandText closure <> ", i32 0, i32 0")
    code <- emitResult Ptr ("load ptr, ptr " <> operandText codeAddress)
    environmentAddress <- emitResult Ptr
      ("getelementptr inbounds { ptr, ptr, ptr }, ptr " <> operandText closure <> ", i32 0, i32 1")
    environment <- emitResult Ptr ("load ptr, ptr " <> operandText environmentAddress)
    emitResult range
      ("call " <> renderType range <> " " <> operandText code <> "(ptr " <> operandText environment <> ", " <> typed actual <> ")")
  actualType -> failCodegen source "llvm-call-type"
    ("Attempted to apply a value of type " <> renderType actualType)

forceExpected :: ModuleContext -> LlvmType -> Deferred -> Codegen Operand
forceExpected context expected deferred = case deferred of
  DeferredExpr expression -> lowerExpected context expected expression
  Lowered value -> ensureOperand noExpression expected value >> pure value
  where
    noExpression = Located noSpan (M.ERecord [])

lowerGlobalClosure :: ModuleContext -> M.Expr -> FunctionInfo -> [Operand] -> Codegen Operand
lowerGlobalClosure context source info supplied = do
  let parameters = functionParameters info
  if length supplied > length parameters
    then failCodegen source "llvm-partial-application" "A global closure captures more arguments than its function accepts"
    else pure ()
  forM_ (zip supplied parameters) $ \(actual, (_, expected)) -> ensureOperand source expected actual
  let remaining = drop (length supplied) parameters
  case remaining of
    [] -> emitResult (functionResult info)
      ("call " <> renderType (functionResult info) <> " " <> functionName info
        <> "(" <> intercalate ", " (map typed supplied) <> ")")
    _ -> lowerPartialClosure context source info supplied remaining

lowerPartialClosure :: ModuleContext -> M.Expr -> FunctionInfo -> [Operand] -> [(String, LlvmType)] -> Codegen Operand
lowerPartialClosure context source info supplied remaining = do
  helperName <- freshHelperName "partial"
  let parameters = functionParameters info
  (domain, range) <- case remaining of
    (_, firstType) : rest -> pure (firstType, foldr (Function . snd) (functionResult info) rest)
    [] -> failCodegen source "llvm-partial-application" "Internal partial application has no remaining parameter"
  let closureType = Function domain range
  environment <- allocateEnvironment supplied
  let helperInitial = initialCodegenState helperName []
      buildHelper = do
        restored <- restoreEnvironment supplied
        let argument = Operand domain "%argument"
            allArguments = restored <> [argument]
        if length allArguments == length parameters
          then do
            forM_ (zip allArguments parameters) $ \(actual, (_, expected)) -> ensureOperand source expected actual
            emitResult (functionResult info)
              ("call " <> renderType (functionResult info) <> " " <> functionName info
                <> "(" <> intercalate ", " (map typed allArguments) <> ")")
          else lowerGlobalClosure context source info allArguments
  (result, helperFinal) <- liftEither (runStateT buildHelper helperInitial)
  ensureOperand source range result
  addHelperDefinition helperName domain range result helperFinal
  allocateClosure helperName closureType environment Nothing

lowerLambdaClosure
  :: ModuleContext
  -> M.Expr
  -> String
  -> M.Type
  -> M.Type
  -> M.Expr
  -> Codegen Operand
lowerLambdaClosure context source _name domainType rangeType body = do
  domain <- liftEither (lowerTypeAt (locatedSpan source) domainType)
  range <- liftEither (lowerTypeAt (locatedSpan source) rangeType)
  captures <- gets codegenLocals
  helperName <- freshHelperName "lambda"
  environment <- allocateEnvironment captures
  let helperInitial = initialCodegenState helperName []
      buildHelper = do
        restored <- restoreEnvironment captures
        modify' (\state -> state {codegenLocals = Operand domain "%argument" : restored})
        lowerExpected context range body
  (result, helperFinal) <- liftEither (runStateT buildHelper helperInitial)
  ensureOperand source range result
  addHelperDefinition helperName domain range result helperFinal
  browserLiteral <- lowerBrowserClosureLiteral context source captures
  allocateClosure helperName (Function domain range) environment browserLiteral

lowerBrowserClosureLiteral
  :: ModuleContext
  -> M.Expr
  -> [Operand]
  -> Codegen (Maybe Operand)
lowerBrowserClosureLiteral context source locals =
  case Map.lookup source (moduleClientClosures context) of
    Nothing -> pure Nothing
    Just identifier -> do
      let indices = Map.findWithDefault [] source (moduleClosureCaptures context)
          captureTypes = Map.findWithDefault [] source (moduleClosureCaptureTypes context)
      if length indices == length captureTypes
        then pure ()
        else failCodegen source "llvm-client-closure"
          "Browser closure capture metadata is inconsistent"
      captures <- mapM captureAt (zip indices captureTypes)
      body <- foldM appendCapture
        (stringOperand context (ByteString8.pack (clientClosureStart identifier)))
        (zip [0 :: Int ..] captures)
      completed <- lowerStringConcatOperands source body
        (stringOperand context (ByteString8.pack "])"))
      pure (Just completed)
  where
    captureAt (index, typ) = case drop index locals of
      value : _ -> lowerClientCapture context source typ value
      [] -> failCodegen source "llvm-client-closure"
        ("Browser closure refers to unavailable local " <> show index)
    appendCapture rendered (index, capture) = do
      separated <- if index == 0
        then pure rendered
        else lowerStringConcatOperands source rendered
          (stringOperand context (ByteString8.pack ","))
      lowerStringConcatOperands source separated capture

lowerExpected :: ModuleContext -> LlvmType -> M.Expr -> Codegen Operand
lowerExpected context expected expression
  | Function I8 range <- expected
  , not (obviousFunctionValue context expression) =
      lowerActionClosure context expression range
  | M.ESqlCache {} <- locatedValue expression = runCacheNode
  | M.ESqlCacheFlush {} <- locatedValue expression = runCacheNode
  | otherwise = do
      value <- lowerExpr context expression
      ensureOperand expression expected value
      pure value
  where
    runCacheNode = do
      action <- lowerExpr context expression
      runTransactionToType context expression expected action

runTransactionToType
  :: ModuleContext
  -> M.Expr
  -> LlvmType
  -> Operand
  -> Codegen Operand
runTransactionToType context source expected value
  | operandType value == expected = pure value
  | Function I8 _ <- operandType value = do
      next <- applyClosure context source value (Lowered (Operand I8 "0"))
      runTransactionToType context source expected next
  | otherwise = failCodegen source "llvm-transaction-result"
      ("Transaction produced " <> renderType (operandType value)
        <> " instead of " <> renderType expected)

-- Vr currently reaches Mono one normalization step earlier than Ur/Web for
-- primitive transactions: an action such as debug "x" is an expression whose
-- declared value is unit -> unit, but it is not yet wrapped in EAbs.  Preserve
-- call-by-value function semantics by materializing that missing unit thunk at
-- the native ABI boundary.
lowerActionClosure :: ModuleContext -> M.Expr -> LlvmType -> Codegen Operand
lowerActionClosure context action range = do
  captures <- gets codegenLocals
  helperName <- freshHelperName "transaction"
  environment <- allocateEnvironment captures
  let helperInitial = initialCodegenState helperName []
      buildHelper = do
        restored <- restoreEnvironment captures
        modify' (\state -> state {codegenLocals = restored})
        value <- lowerExpr context action
        runTransactionOperand context action value
  (result, helperFinal) <- liftEither (runStateT buildHelper helperInitial)
  ensureOperand action range result
  addHelperDefinition helperName I8 range result helperFinal
  browserLiteral <- lowerBrowserClosureLiteral context action captures
  allocateClosure helperName (Function I8 range) environment browserLiteral

obviousFunctionValue :: ModuleContext -> M.Expr -> Bool
obviousFunctionValue context expression = case locatedValue expression of
  M.EAbs {} -> True
  M.ERel {} -> True
  M.EClosure {} -> True
  M.ENamed identifier -> Map.member identifier (moduleFunctions context)
  M.EApp {} ->
    let (headExpression, arguments) = collectApplications expression
     in case locatedValue headExpression of
          M.ENamed identifier -> case Map.lookup identifier (moduleFunctions context) of
            Just info
              | length arguments < length (functionParameters info) -> True
              | length arguments == length (functionParameters info) -> isFunctionType (functionResult info)
              | otherwise -> False
            Nothing -> False
          M.EAbs {} -> True
          M.ERel {} -> True
          M.EClosure {} -> True
          _ -> False
  _ -> False

isFunctionType :: LlvmType -> Bool
isFunctionType Function {} = True
isFunctionType _ = False

freshHelperName :: String -> Codegen String
freshHelperName purpose = do
  prefix <- gets codegenHelperPrefix
  helperIndex <- gets codegenNextHelper
  modify' (\state -> state {codegenNextHelper = helperIndex + 1})
  pure (prefix <> "_" <> purpose <> "_" <> show helperIndex)

environmentType :: [Operand] -> LlvmType
environmentType values = Record
  [("capture" <> show index, operandType value) | (index, value) <- zip [0 :: Int ..] values]

allocateEnvironment :: [Operand] -> Codegen Operand
allocateEnvironment [] = pure (Operand Ptr "null")
allocateEnvironment values = do
  let typ = environmentType values
  allocation <- allocate typ
  forM_ (zip [0 :: Int ..] values) $ \(index, value) -> do
    address <- emitResult Ptr
      ("getelementptr inbounds " <> renderType typ <> ", ptr " <> operandText allocation <> ", i32 0, i32 " <> show index)
    emitInstruction ("store " <> typed value <> ", ptr " <> operandText address)
  pure allocation

restoreEnvironment :: [Operand] -> Codegen [Operand]
restoreEnvironment values = forM (zip [0 :: Int ..] values) $ \(index, value) -> do
  let typ = environmentType values
  address <- emitResult Ptr
    ("getelementptr inbounds " <> renderType typ <> ", ptr %environment, i32 0, i32 " <> show index)
  emitResult (operandType value) ("load " <> renderType (operandType value) <> ", ptr " <> operandText address)

allocateClosure :: String -> LlvmType -> Operand -> Maybe Operand -> Codegen Operand
allocateClosure helperName closureType environment browserLiteral = do
  closure <- allocate (Record [("code", Ptr), ("environment", Ptr), ("browserLiteral", Ptr)])
  codeAddress <- emitResult Ptr
    ("getelementptr inbounds { ptr, ptr, ptr }, ptr " <> operandText closure <> ", i32 0, i32 0")
  emitInstruction ("store ptr @" <> helperName <> ", ptr " <> operandText codeAddress)
  environmentAddress <- emitResult Ptr
    ("getelementptr inbounds { ptr, ptr, ptr }, ptr " <> operandText closure <> ", i32 0, i32 1")
  emitInstruction ("store " <> typed environment <> ", ptr " <> operandText environmentAddress)
  browserLiteralAddress <- emitResult Ptr
    ("getelementptr inbounds { ptr, ptr, ptr }, ptr " <> operandText closure <> ", i32 0, i32 2")
  emitInstruction ("store ptr " <> maybe "null" operandText browserLiteral
    <> ", ptr " <> operandText browserLiteralAddress)
  pure (Operand closureType (operandText closure))

addHelperDefinition :: String -> LlvmType -> LlvmType -> Operand -> CodegenState -> Codegen ()
addHelperDefinition helperName domain range result helperFinal = do
  let instructions = reverse (codegenInstructions helperFinal)
      definition = unlines
        ([ "define internal " <> renderType range <> " @" <> helperName
             <> "(ptr %environment, " <> renderType domain <> " %argument) {"
         , "entry:"
          ]
          <> map ("  " <>) instructions
          <> ["  ret " <> typed result, "}", ""])
      nested = reverse (codegenHelpers helperFinal)
  modify' (\state -> state {codegenHelpers = reverse (nested <> [definition]) <> codegenHelpers state})

lowerForeignIntrinsic
  :: ModuleContext
  -> M.Expr
  -> ForeignInfo
  -> [Deferred]
  -> Codegen Operand
lowerForeignIntrinsic context source info arguments = do
  (domains, result) <- liftEither (foreignRuntimeShape info)
  function <- lowerForeignValue context source info [] domains result
  foldM (applyClosure context source) function arguments

lowerForeignValue
  :: ModuleContext
  -> M.Expr
  -> ForeignInfo
  -> [Operand]
  -> [LlvmType]
  -> LlvmType
  -> Codegen Operand
lowerForeignValue context source info supplied remaining result = case remaining of
  []
    | foreignIsTransactional info ->
        makeUnitClosure context source ("ffi_" <> sanitize (foreignLabel info)) result supplied
          (emitForeignCall source info result)
    | otherwise -> emitForeignCall source info result supplied
  domain : rest -> do
    helperName <- freshHelperName ("ffi_" <> sanitize (foreignLabel info))
    environment <- allocateEnvironment supplied
    let range = foldr Function terminal rest
        terminal
          | foreignIsTransactional info = Function I8 result
          | otherwise = result
        helperInitial = initialCodegenState helperName []
        buildHelper = do
          restored <- restoreEnvironment supplied
          lowerForeignValue context source info (restored <> [Operand domain "%argument"]) rest result
    (value, helperFinal) <- liftEither (runStateT buildHelper helperInitial)
    ensureOperand source range value
    addHelperDefinition helperName domain range value helperFinal
    allocateClosure helperName (Function domain range) environment Nothing

emitForeignCall
  :: M.Expr
  -> ForeignInfo
  -> LlvmType
  -> [Operand]
  -> Codegen Operand
emitForeignCall source info result arguments = do
  (sourceDomains, sourceResult) <- liftEither (foreignSourceShape info)
  if length sourceDomains /= length arguments
    then failCodegen source "llvm-ffi-arity"
      (foreignLabel info <> " expected " <> show (length sourceDomains)
        <> " arguments but received " <> show (length arguments))
    else pure ()
  context <- emitResult Ptr "call ptr @vr_runtime_current_context()"
  converted <- sequence
    [ convertForeignArgument source typ argument
    | (typ, argument) <- zip sourceDomains arguments
    ]
  abiResult <- liftEither (foreignSourceAbiType (locatedSpan source) sourceResult)
  let renderedArguments = typed context : zipWith renderForeignArgument sourceDomains converted
  if isIndirectForeignSourceType sourceResult
    then do
      allocation <- allocate abiResult
      emitInstruction
        ("call void " <> foreignSymbol info <> "(ptr sret(" <> renderType abiResult <> ") "
          <> operandText allocation <> ", " <> intercalate ", " renderedArguments <> ")")
      ensureOperand source result allocation
      pure allocation
    else do
      raw <- emitResult abiResult
        ("call " <> renderType abiResult <> " " <> foreignSymbol info
          <> "(" <> intercalate ", " renderedArguments <> ")")
      convertForeignResult source sourceResult result raw

renderForeignArgument :: M.Type -> Operand -> String
renderForeignArgument sourceType argument
  | isIndirectForeignSourceType sourceType =
      "ptr byval(" <> renderType (indirectForeignAbiType sourceType)
        <> ") " <> operandText argument
  | otherwise = typed argument

indirectForeignAbiType :: M.Type -> LlvmType
indirectForeignAbiType sourceType = case locatedValue sourceType of
  M.TFfi "Basis" "postBody" -> foreignPostBodyAbiType
  _ -> foreignFileAbiType

foreignFileAbiType :: LlvmType
foreignFileAbiType = Record
  [ ("name", Ptr)
  , ("type", Ptr)
  , ("data", Record [("size", I64), ("data", Ptr)])
  ]

convertForeignArgument :: M.Expr -> M.Type -> Operand -> Codegen Operand
convertForeignArgument source sourceType value = case locatedValue sourceType of
  M.TFfi "Basis" "client" -> do
    ensureOperand source Ptr value
    emitResult I32 ("call i32 @vr_runtime_client_number(" <> typed value <> ")")
  M.TFfi "Basis" "channel" -> do
    ensureOperand source Ptr value
    client <- emitResult I32
      ("call i32 @vr_runtime_channel_client(" <> typed value <> ")")
    number <- emitResult I32
      ("call i32 @vr_runtime_channel_number(" <> typed value <> ")")
    client64 <- emitResult I64 ("zext i32 " <> operandText client <> " to i64")
    number64 <- emitResult I64 ("zext i32 " <> operandText number <> " to i64")
    shifted <- emitResult I64 ("shl i64 " <> operandText client64 <> ", 32")
    emitResult I64
      ("or i64 " <> operandText shifted <> ", " <> operandText number64)
  M.TFfi "Basis" "time" -> do
    ensureOperand source Ptr value
    let internalType = Record [("seconds", I64), ("microseconds", I64)]
    aggregate <- emitResult internalType
      ("load " <> renderType internalType <> ", ptr " <> operandText value)
    seconds <- emitResult I64
      ("extractvalue " <> renderType internalType <> " " <> operandText aggregate <> ", 0")
    microseconds64 <- emitResult I64
      ("extractvalue " <> renderType internalType <> " " <> operandText aggregate <> ", 1")
    microseconds <- emitResult I32
      ("trunc i64 " <> operandText microseconds64 <> " to i32")
    buildRecordOperand source [("seconds", seconds), ("microseconds", microseconds)]
  M.TFfi "Basis" "blob" -> loadAggregate
    (Record [("size", I64), ("data", Ptr)])
  M.TFfi "Basis" "file" -> ensureOperand source Ptr value >> pure value
  M.TFfi "Basis" "postBody" -> do
    ensureOperand source Ptr value
    contentType <- emitResult Ptr
      ("call ptr @vr_runtime_post_type(" <> typed value <> ")")
    dataValue <- emitResult Ptr
      ("call ptr @vr_runtime_post_data(" <> typed value <> ")")
    contentLength <- emitResult I64
      ("call i64 @vr_runtime_post_length(" <> typed value <> ")")
    aggregate <- buildRecordOperand source
      [("type", contentType), ("data", dataValue), ("length", contentLength)]
    allocation <- allocate foreignPostBodyAbiType
    emitInstruction ("store " <> typed aggregate <> ", ptr " <> operandText allocation)
    pure allocation
  _ -> case operandType value of
    I1 -> emitResult I32 ("zext i1 " <> operandText value <> " to i32")
    I8 -> emitResult I32 ("zext i8 " <> operandText value <> " to i32")
    Function {} -> failCodegen source "llvm-ffi-type"
      "Passing Ur function closures through the C FFI is not supported"
    _ -> pure value
  where
    loadAggregate typ = do
      ensureOperand source Ptr value
      emitResult typ ("load " <> renderType typ <> ", ptr " <> operandText value)

convertForeignResult :: Located value -> M.Type -> LlvmType -> Operand -> Codegen Operand
convertForeignResult source sourceType expected raw = case locatedValue sourceType of
  M.TFfi "Basis" "client" -> do
    ensureOperand source I32 raw
    value <- emitResult Ptr
      ("call ptr @vr_runtime_client_from_number(" <> typed raw <> ")")
    ensureOperand source expected value
    pure value
  M.TFfi "Basis" "channel" -> do
    ensureOperand source I64 raw
    shifted <- emitResult I64 ("lshr i64 " <> operandText raw <> ", 32")
    client <- emitResult I32
      ("trunc i64 " <> operandText shifted <> " to i32")
    number <- emitResult I32
      ("trunc i64 " <> operandText raw <> " to i32")
    value <- emitResult Ptr
      ("call ptr @vr_runtime_channel_lookup_public("
        <> typed client <> ", " <> typed number <> ")")
    ensureOperand source expected value
    pure value
  M.TFfi "Basis" "time" -> do
    let abiType = Record [("seconds", I64), ("microseconds", I32)]
        internalType = Record [("seconds", I64), ("microseconds", I64)]
    ensureOperand source abiType raw
    seconds <- emitResult I64
      ("extractvalue " <> renderType abiType <> " " <> operandText raw <> ", 0")
    microseconds32 <- emitResult I32
      ("extractvalue " <> renderType abiType <> " " <> operandText raw <> ", 1")
    microseconds <- emitResult I64
      ("zext i32 " <> operandText microseconds32 <> " to i64")
    aggregate <- buildRecordOperand source
      [("seconds", seconds), ("microseconds", microseconds)]
    allocation <- allocate internalType
    emitInstruction ("store " <> typed aggregate <> ", ptr " <> operandText allocation)
    ensureOperand source expected allocation
    pure allocation
  M.TFfi "Basis" "blob" -> storeAggregate
    (Record [("size", I64), ("data", Ptr)])
  M.TFfi "Basis" "file" -> storeAggregate foreignFileAbiType
  _ -> case (expected, operandType raw) of
    (I1, I32) -> emitResult I1 ("trunc i32 " <> operandText raw <> " to i1")
    (I8, I32) -> emitResult I8 ("trunc i32 " <> operandText raw <> " to i8")
    _ -> ensureOperand source expected raw >> pure raw
  where
    storeAggregate typ = do
      ensureOperand source typ raw
      allocation <- allocate typ
      emitInstruction ("store " <> typed raw <> ", ptr " <> operandText allocation)
      ensureOperand source expected allocation
      pure allocation

lowerIntrinsic :: ModuleContext -> M.Expr -> String -> String -> [M.StaticArg] -> [Deferred] -> Codegen Operand
lowerIntrinsic context source moduleName name staticArguments arguments
  | moduleName /= "Basis" = case Map.lookup (moduleName, name) (moduleForeignFunctions context) of
      Just info -> lowerForeignIntrinsic context source info arguments
      Nothing -> failCodegen source "llvm-ffi"
        ("Native FFI function has no preserved signature: " <> moduleName <> "." <> name)
  | otherwise = case (name, arguments) of
      ("transaction_return", [value]) -> force context value
      ("transaction_bind", [action, continuation]) -> do
        value <- runDeferredTransaction context source action
        continuationExpr <- deferredExpression source continuation
        next <- applyValue context continuationExpr [value]
        runTransactionOperand context source next
      ("self", []) -> emitResult Ptr "call ptr @vr_runtime_current_client()"
      ("debug", [message]) -> do
        value <- force context message
        ensureOperand source Ptr value
        stream <- emitResult Ptr "load ptr, ptr @stderr"
        _ <- emitResult I32 ("call i32 @fputs(" <> typed value <> ", " <> typed stream <> ")")
        _ <- emitResult I32 ("call i32 @fputc(i32 10, " <> typed stream <> ")")
        pure (Operand I8 "0")
      ("sleep", [duration]) -> force context duration >>= lowerSleepOperand source
      ("spawn", [action]) -> deferredExpression source action >>= lowerSpawn context source
      ("new_client_source", [value]) -> do
        value' <- force context value
        ensureOperand source Ptr value'
        emitResult Ptr ("call ptr @vr_runtime_client_source_new(" <> typed value' <> ")")
      ("set_client_source", [clientSource, value]) -> do
        clientSource' <- force context clientSource
        value' <- force context value
        ensureOperand source Ptr clientSource'
        ensureOperand source Ptr value'
        emitInstruction
          ("call void @vr_runtime_client_source_set(" <> typed clientSource' <> ", " <> typed value' <> ")")
        pure (Operand I8 "0")
      ("filecache_missed", []) ->
        emitResult I1 "call i1 @vr_runtime_file_cache_missed()"
      ("check_filecache", [hash]) -> do
        hash' <- force context hash
        ensureOperand source Ptr hash'
        emitResult Ptr
          ("call ptr @vr_runtime_file_cache_check(" <> typed hash' <> ")")
      ("cache_file", [contents]) -> do
        contents' <- force context contents
        ensureOperand source Ptr contents'
        emitInstruction
          ("call void @vr_runtime_file_cache_store(" <> typed contents' <> ")")
        pure (Operand I8 "0")
      ("channel", []) -> emitResult Ptr "call ptr @vr_runtime_channel_new()"
      ("send", [channel, value]) -> do
        channel' <- force context channel
        value' <- force context value
        ensureOperand source Ptr channel'
        payloadType <- case staticArguments of
          argument : _ -> liftEither (staticMonoTypeAt (locatedSpan source) argument)
          [] -> failCodegen source "llvm-channel-type" "Channel send is missing its resolved payload type"
        serialized <- lowerUrlEncode context source payloadType value'
        boxed <- allocate (operandType value')
        emitInstruction ("store " <> typed value' <> ", ptr " <> operandText boxed)
        emitInstruction
          ("call void @vr_runtime_channel_send(" <> typed channel' <> ", " <> typed boxed
            <> ", " <> typed serialized <> ")")
        pure (Operand I8 "0")
      ("recv", [channel]) -> do
        typ <- staticResultType source staticArguments
        channelExpr <- deferredExpression source channel
        lowerReceive context source channelExpr (llvmTypeToMonoType (locatedSpan source) typ)
      ("rand", []) -> emitResult I64 "call i64 @vr_runtime_rand()"
      ("make", [value]) -> lowerPolymorphicVariantMake context source staticArguments value
      ("match", [variant, handlers]) ->
        lowerPolymorphicVariantMatch context source staticArguments variant handlers
      ("subform", [xml]) -> lowerSubform context source ".b" staticArguments xml
      ("subforms", [xml]) -> lowerSubform context source ".s" staticArguments xml
      ("entry", [xml]) -> lowerSubformEntry context source xml
      (evidence, []) | evidence `elem` ["fieldsOf_table", "fieldsOf_view", "sql_subset", "sql_subset_all"] ->
        pure (Operand I8 "0")
      ("sql_subset_concat", [_left, _right]) -> pure (Operand I8 "0")
      ("sql_from_nil", []) -> pure (stringOperand context ByteString.empty)
      ("sql_from_table", [table]) -> lowerSqlFrom context source staticArguments False table
      ("sql_from_table", [_fieldsEvidence, table]) -> lowerSqlFrom context source staticArguments False table
      ("sql_from_query", [query]) -> lowerSqlFrom context source staticArguments True query
      ("sql_from_comma", [left, right]) -> lowerSqlComma context source left right
      ("sql_inner_join", values)
        | predicate : right : left : _ <- reverse values ->
            lowerSqlJoin context source " JOIN " left right predicate
      ("sql_left_join", values)
        | predicate : right : left : _ <- reverse values ->
            lowerSqlJoin context source " LEFT JOIN " left right predicate
      ("sql_right_join", values)
        | predicate : right : left : _ <- reverse values ->
            lowerSqlJoin context source " RIGHT JOIN " left right predicate
      ("sql_full_join", values)
        | predicate : right : left : _ <- reverse values ->
            lowerSqlJoin context source " FULL JOIN " left right predicate
      ("sql_no_limit", []) -> pure (stringOperand context ByteString.empty)
      ("sql_limit", [limit]) -> lowerSqlNumberClause context source " LIMIT " limit
      ("sql_no_offset", []) -> pure (stringOperand context ByteString.empty)
      ("sql_offset", [offset]) -> lowerSqlNumberClause context source " OFFSET " offset
      ("sql_order_by_Nil", []) -> pure (stringOperand context ByteString.empty)
      ("sql_order_by_random", []) -> pure (stringOperand context (ByteString8.pack "RANDOM()"))
      ("sql_asc", []) -> pure (stringOperand context ByteString.empty)
      ("sql_desc", []) -> pure (stringOperand context (ByteString8.pack " DESC"))
      ("sql_order_by_Cons", [expression, direction, rest]) ->
        lowerSqlOrder context source expression direction rest
      ("sql_order_by_Cons", values)
        | rest : direction : expression : _ <- reverse values ->
            lowerSqlOrder context source expression direction rest
      ("sql_query1", [record]) -> lowerSqlQuery1 context source staticArguments record
      ("sql_query", [record]) -> lowerSqlQuery context source record
      ("query", [query, callback, initial]) ->
        lowerSqlFold context source staticArguments query callback initial
      ("no_primary_key", []) -> pure (stringOperand context ByteString.empty)
      ("primary_key", _) -> lowerPrimaryKey context source staticArguments
      ("no_constraint", []) -> pure (Operand I8 "0")
      ("one_constraint", values)
        | constraint : _ <- reverse values ->
            lowerOneConstraint context source staticArguments constraint
      ("join_constraints", values)
        | right : left : _ <- reverse values ->
            lowerConstraintJoin context source left right
      ("unique", _) -> lowerUnique context source staticArguments
      ("mat_nil", []) -> lowerMatchingNil context source
      ("mat_cons", values)
        | matching : _ <- reverse values ->
            lowerMatchingCons context source staticArguments matching
      ("restrict", []) -> pure (stringOperand context (ByteString8.pack "RESTRICT"))
      ("cascade", []) -> pure (stringOperand context (ByteString8.pack "CASCADE"))
      ("no_action", []) -> pure (stringOperand context (ByteString8.pack "NO ACTION"))
      ("set_null", []) -> pure (stringOperand context (ByteString8.pack "SET NULL"))
      ("foreign_key", values)
        | properties : table : matching : _ <- reverse values ->
            lowerForeignKey context source matching table properties
      ("sql_exp_weaken", values)
        | expression : _ <- reverse values -> force context expression
      ("check", values)
        | expression : _ <- reverse values -> lowerCheckConstraint context source expression
      ("sql_window", values)
        | expression : _ <- reverse values -> force context expression
      ("sql_count_col", []) -> pure (stringOperand context (ByteString8.pack "COUNT"))
      ("sql_avg", [_]) -> pure (stringOperand context (ByteString8.pack "AVG"))
      ("sql_sum", [_, _]) -> pure (stringOperand context (ByteString8.pack "SUM"))
      ("sql_max", [_, _]) -> pure (stringOperand context (ByteString8.pack "MAX"))
      ("sql_min", [_, _]) -> pure (stringOperand context (ByteString8.pack "MIN"))
      ("sql_aggregate", [operator, expression]) ->
        lowerSqlAggregate context source operator expression
      ("sql_field", []) -> lowerSqlField context source staticArguments
      ("sql_exp", []) -> case [field | M.StaticName field <- staticArguments] of
        [] -> failCodegen source "llvm-sql-expression" "SQL expression has no resolved name"
        fields -> pure (stringOperand context (ByteString8.pack (last fields)))
      ("sql_true", []) -> pure (stringOperand context (ByteString8.pack "1"))
      ("sql_false", []) -> pure (stringOperand context (ByteString8.pack "0"))
      ("sql_is_null", [value]) -> lowerSqlIsNull context source value
      ("sql_coalesce", [left, right]) -> lowerSqlCall2 context source "COALESCE(" left right
      ("sql_if_then_else", [condition, yes, no]) -> lowerSqlIf context source condition yes no
      ("sql_nfunc", [function]) -> force context function
      ("sql_current_timestamp", []) ->
        pure (stringOperand context (ByteString8.pack "CURRENT_TIMESTAMP"))
      ("sql_distance", [_evidence]) -> pure (stringOperand context (ByteString8.pack
        (if moduleDatabaseSystem context == DatabasePostgres then "<->" else "vr_trigram_distance")))
      ("sql_octet_length", []) -> pure (stringOperand context (ByteString8.pack "length"))
      ("sql_lower", []) -> pure (stringOperand context (ByteString8.pack "lower"))
      ("sql_upper", []) -> pure (stringOperand context (ByteString8.pack "upper"))
      ("sql_ufunc", [function, value]) -> lowerSqlCall1 context source function value
      ("sql_similarity", [_evidence]) ->
        pure (stringOperand context (ByteString8.pack
          (if moduleDatabaseSystem context == DatabasePostgres then "similarity" else "vr_trigram_similarity")))
      ("sql_bfunc", [function, left, right]) ->
        lowerSqlNamedCall2 context source function left right
      ("sql_no_partition", []) -> pure (stringOperand context ByteString.empty)
      ("sql_partition", [expression]) -> lowerSqlPartition context source expression
      ("sql_window_aggregate", [operator, expression]) ->
        lowerSqlCall1 context source operator expression
      ("sql_window_count", []) -> pure (stringOperand context (ByteString8.pack "COUNT(*)"))
      ("sql_rank", []) -> pure (stringOperand context (ByteString8.pack "RANK()"))
      ("sql_window_function", [window, partition, order]) ->
        lowerSqlWindowFunction context source window partition order
      (operator, _) | Just sqlOperator <- sqlOperatorText operator ->
        pure (stringOperand context (ByteString8.pack sqlOperator))
      ("sql_unary", [operator, value]) -> lowerSqlUnary context source operator value
      ("sql_binary", [operator, left, right]) -> lowerSqlBinary context source operator left right
      ("sql_count", []) -> pure (stringOperand context (ByteString8.pack "COUNT(*)"))
      ("sql_int", []) -> makeSqlRuntimeEncoder source "sql_int" I64 "vr_runtime_urlify_int"
      ("sql_float", []) -> makeSqlRuntimeEncoder source "sql_float" F64 "vr_runtime_show_float"
      ("sql_bool", []) -> makeSqlRuntimeEncoder source "sql_bool" I1 "vr_runtime_sql_bool"
      ("sql_string", []) -> makeSqlRuntimeEncoder source "sql_string" Ptr "vr_runtime_sql_string"
      ("sql_char", []) -> makeUnaryClosure source "sql_char" I32 Ptr [] $ \_ argument -> do
        shown <- emitResult Ptr ("call ptr @vr_runtime_show_char(" <> typed argument <> ")")
        emitResult Ptr ("call ptr @vr_runtime_sql_string(" <> typed shown <> ")")
      ("sql_time", []) -> makeSqlRuntimeEncoder source "sql_time" Ptr "vr_runtime_sql_time"
      ("sql_blob", []) -> makeSqlRuntimeEncoder source "sql_blob" Ptr "vr_runtime_sql_blob"
      ("sql_client", []) -> makeSqlRuntimeEncoder source "sql_client" Ptr "vr_runtime_sql_client"
      ("sql_channel", []) -> makeSqlRuntimeEncoder source "sql_channel" Ptr "vr_runtime_sql_channel"
      (encoder, []) | encoder `elem` ["sql_url", "sql_serialized"] ->
        makeSqlRuntimeEncoder source encoder Ptr "vr_runtime_sql_string"
      ("sql_prim", [encoder]) -> force context encoder
      ("sql_option_prim", [encoder]) -> do
        encoder' <- force context encoder
        elementType <- case operandType encoder' of
          Function domain Ptr -> pure domain
          actual -> failCodegen source "llvm-sql-encoder"
            ("SQL option encoder received " <> renderType actual)
        makeUnaryClosure source "sql_option" Ptr Ptr [encoder'] $ \captures option -> case captures of
          [capturedEncoder] -> lowerSqlOption context source elementType capturedEncoder option
          _ -> failCodegen source "llvm-sql-encoder" "Internal SQL option capture mismatch"
      ("sql_inject", [encoder, value]) -> do
        encoder' <- force context encoder
        value' <- force context value
        applyClosure context source encoder' (Lowered value')
      ("insert", [table, fields]) -> lowerSqlInsert context source staticArguments table fields
      ("delete", [table, predicate]) -> lowerSqlDelete context source table predicate
      ("update", [fields, table, predicate]) -> lowerSqlUpdate context source fields table predicate
      ("dml", [command]) -> do
        command' <- force context command
        ensureOperand source Ptr command'
        makeUnitClosure context source "dml" I8 [command'] $ \captures -> case captures of
          [capturedCommand] -> do
            emitInstruction ("call void @vr_runtime_database_exec(" <> typed capturedCommand <> ")")
            pure (Operand I8 "0")
          _ -> failCodegen source "llvm-dml" "Internal DML capture mismatch"
      ("tryDml", [command]) -> do
        command' <- force context command
        ensureOperand source Ptr command'
        makeUnitClosure context source "try_dml" Ptr [command'] $ \captures -> case captures of
          [capturedCommand] -> lowerTryDml context source capturedCommand
          _ -> failCodegen source "llvm-dml" "Internal tryDml capture mismatch"
      ("nextval", [sequenceName]) -> lowerNextval context source sequenceName
      ("setval", [sequenceName, value]) -> lowerSetval context source sequenceName value
      ("error", [message]) -> do
        resultType <- staticResultType source staticArguments
        message' <- force context message
        ensureOperand source Ptr message'
        emitInstruction ("call void @vr_runtime_fail(" <> typed message' <> ")")
        pure (zeroOperand resultType)
      ("readError", [_dictionary, value])
        | isBasisStatic "int" staticArguments -> lowerStringUnary context source I64 "vr_runtime_read_int_error" value
        | isBasisStatic "float" staticArguments -> lowerStringUnary context source F64 "vr_runtime_read_float_error" value
        | isBasisStatic "char" staticArguments -> lowerStringUnary context source I32 "vr_runtime_read_char_error" value
        | isBasisStatic "bool" staticArguments -> lowerStringUnary context source I1 "vr_runtime_read_bool_error" value
        | isStringStatic staticArguments -> force context value
      ("stringToInt", [value]) -> lowerParsedOption context source I64 "vr_runtime_read_int" value
      ("stringToFloat", [value]) -> lowerParsedOption context source F64 "vr_runtime_read_float" value
      ("stringToChar", [value]) -> lowerParsedOption context source I32 "vr_runtime_read_char" value
      ("stringToBool", [value]) -> lowerParsedOption context source I1 "vr_runtime_read_bool" value
      ("stringToInt_error", [value]) -> lowerStringUnary context source I64 "vr_runtime_read_int_error" value
      ("stringToFloat_error", [value]) -> lowerStringUnary context source F64 "vr_runtime_read_float_error" value
      ("stringToChar_error", [value]) -> lowerStringUnary context source I32 "vr_runtime_read_char_error" value
      ("stringToBool_error", [value]) -> lowerStringUnary context source I1 "vr_runtime_read_bool_error" value
      ("eq_time", [left, right]) -> lowerStringPair context source I1 "vr_runtime_eq_time" left right
      ("lt_time", [left, right]) -> lowerStringPair context source I1 "vr_runtime_lt_time" left right
      ("le_time", [left, right]) -> lowerStringPair context source I1 "vr_runtime_le_time" left right
      ("now", []) -> emitResult Ptr "call ptr @vr_runtime_now()"
      ("minTime", []) -> emitResult Ptr "call ptr @vr_runtime_min_time()"
      ("addSeconds", [value, seconds]) -> lowerTimeIntBinary context source Ptr "vr_runtime_add_seconds" value seconds
      ("toSeconds", [value]) -> lowerStringUnary context source I64 "vr_runtime_to_seconds" value
      ("diffInSeconds", [first, second]) -> lowerStringPair context source I64 "vr_runtime_diff_in_seconds" first second
      ("toMilliseconds", [value]) -> lowerStringUnary context source I64 "vr_runtime_to_milliseconds" value
      ("fromMilliseconds", [value]) -> lowerIntUnary context source Ptr "vr_runtime_from_milliseconds" value
      ("diffInMilliseconds", [first, second]) -> lowerStringPair context source I64 "vr_runtime_diff_in_milliseconds" first second
      ("timef", [format, value]) -> lowerStringPair context source Ptr "vr_runtime_timef" format value
      ("timeToString", [value]) -> lowerStringUnary context source Ptr "vr_runtime_time_to_string" value
      ("stringToTime", [value]) -> do
        parsed <- lowerStringUnary context source Ptr "vr_runtime_read_time" value
        lowerMaybeString context source parsed
      ("stringToTime_error", [value]) -> lowerStringUnary context source Ptr "vr_runtime_read_time_error" value
      ("readUtc", [value]) -> do
        parsed <- lowerStringUnary context source Ptr "vr_runtime_read_utc" value
        lowerMaybeString context source parsed
      ("fromDatetime", values) | length values == 6 -> lowerFromDatetime context source values
      ("datetimeYear", [value]) -> lowerStringUnary context source I64 "vr_runtime_datetime_year" value
      ("datetimeMonth", [value]) -> lowerStringUnary context source I64 "vr_runtime_datetime_month" value
      ("datetimeDay", [value]) -> lowerStringUnary context source I64 "vr_runtime_datetime_day" value
      ("datetimeHour", [value]) -> lowerStringUnary context source I64 "vr_runtime_datetime_hour" value
      ("datetimeMinute", [value]) -> lowerStringUnary context source I64 "vr_runtime_datetime_minute" value
      ("datetimeSecond", [value]) -> lowerStringUnary context source I64 "vr_runtime_datetime_second" value
      ("datetimeDayOfWeek", [value]) -> lowerStringUnary context source I64 "vr_runtime_datetime_day_of_week" value
      (predicate, [])
        | predicate `elem` ["isalnum", "isalpha", "isblank", "iscntrl", "isdigit", "isgraph",
                            "islower", "isprint", "ispunct", "isspace", "isupper", "isxdigit"] ->
            makeUnaryClosure source predicate I32 I1 [] $ \_ argument ->
              emitResult I1 ("call i1 @vr_runtime_" <> predicate <> "(" <> typed argument <> ")")
      (predicate, [value])
        | predicate `elem` ["isalnum", "isalpha", "isblank", "iscntrl", "isdigit", "isgraph",
                            "islower", "isprint", "ispunct", "isspace", "isupper", "isxdigit"] ->
            lowerCharUnary context source I1 ("vr_runtime_" <> predicate) value
      (conversion, []) | conversion `elem` ["tolower", "toupper"] ->
        makeUnaryClosure source conversion I32 I32 [] $ \_ argument ->
          emitResult I32 ("call i32 @vr_runtime_" <> conversion <> "(" <> typed argument <> ")")
      (conversion, [value]) | conversion `elem` ["tolower", "toupper"] ->
        lowerCharUnary context source I32 ("vr_runtime_" <> conversion) value
      ("ord", [value]) -> do
        character <- force context value
        ensureOperand source I32 character
        emitResult I64 ("zext i32 " <> operandText character <> " to i64")
      ("chr", [value]) -> lowerIntUnary context source I32 "vr_runtime_chr" value
      ("iscodepoint", [value]) -> lowerIntUnary context source I1 "vr_runtime_iscodepoint" value
      ("issingle", [value]) -> do
        character <- force context value
        ensureOperand source I32 character
        emitResult I1 ("icmp ult i32 " <> operandText character <> ", 128")
      ("float", [value]) -> do
        integer <- force context value
        ensureOperand source I64 integer
        emitResult F64 ("sitofp i64 " <> operandText integer <> " to double")
      (rounding, [value]) | rounding `elem` ["ceil", "trunc", "round", "floor"] -> do
        rounded <- lowerFloatUnary context source rounding value
        emitResult I64 ("fptosi double " <> operandText rounded <> " to i64")
      (operation, [value])
        | operation `elem` ["sqrt", "sin", "cos", "log", "exp", "asin", "acos", "atan", "abs"] ->
            lowerFloatUnary context source (if operation == "abs" then "fabs" else operation) value
      ("atan2", [left, right]) -> lowerFloatPair context source "atan2" left right
      ("clear_page", []) -> emitInstruction "call void @vr_runtime_clear_page()" >> pure (Operand I8 "0")
      (operation, [value]) | operation `elem` ["cdata", "htmlifyString"] -> do
        expression <- deferredExpression source value
        raw <- force context value
        ensureOperand source Ptr raw
        if htmlSafeExpression expression
          then pure raw
          else emitResult Ptr ("call ptr @vr_runtime_html_escape(" <> typed raw <> ")")
      ("attrifyString", [value]) ->
        lowerStringUnary context source Ptr "vr_runtime_attrify_string" value
      ("atom", [value]) ->
        lowerStringUnary context source Ptr "vr_runtime_css_atom" value
      ("css_url", [value]) ->
        lowerStringUnary context source Ptr "vr_runtime_css_url" value
      ("property", [value]) ->
        lowerStringUnary context source Ptr "vr_runtime_css_property" value
      ("show", [_dictionary, value]) | isStringStatic staticArguments -> force context value
      ("show", [_dictionary, value]) | isBasisStatic "int" staticArguments -> do
        value' <- force context value
        ensureOperand source I64 value'
        emitResult Ptr ("call ptr @vr_runtime_urlify_int(" <> typed value' <> ")")
      ("show", [_dictionary, value]) | isBasisStatic "float" staticArguments -> do
        value' <- force context value
        ensureOperand source F64 value'
        emitResult Ptr ("call ptr @vr_runtime_show_float(" <> typed value' <> ")")
      ("show", [_dictionary, value]) | isBasisStatic "bool" staticArguments -> do
        value' <- force context value
        ensureOperand source I1 value'
        emitResult Ptr ("call ptr @vr_runtime_show_bool(" <> typed value' <> ")")
      ("show", [_dictionary, value]) | isBasisStatic "char" staticArguments -> do
        value' <- force context value
        ensureOperand source I32 value'
        emitResult Ptr ("call ptr @vr_runtime_show_char(" <> typed value' <> ")")
      ("show", [dictionary, value]) -> do
        dictionary' <- force context dictionary
        value' <- force context value
        applyClosure context source dictionary' (Lowered value')
      ("mkShow", [dictionary]) -> force context dictionary
      ("intToString", [value]) -> lowerUrlifyIntrinsic context source I64 "vr_runtime_urlify_int" value
      ("floatToString", [value]) -> lowerUrlifyIntrinsic context source F64 "vr_runtime_show_float" value
      ("boolToString", [value]) -> lowerUrlifyIntrinsic context source I1 "vr_runtime_show_bool" value
      ("charToString", [value]) -> lowerUrlifyIntrinsic context source I32 "vr_runtime_show_char" value
      ("str1", [value]) -> lowerUrlifyIntrinsic context source I32 "vr_runtime_show_char" value
      ("strlen", [value]) -> lowerStringUnary context source I64 "vr_runtime_strlen" value
      ("strlenUtf8", [value]) -> lowerStringUnary context source I64 "vr_runtime_strlen_utf8" value
      ("strlenGe", [value, wantedLength]) -> lowerStringIntBinary context source I1 "vr_runtime_strlen_ge" value wantedLength
      ("strsub", [value, index]) -> lowerStringIntBinary context source I32 "vr_runtime_strsub" value index
      ("strsubUtf8", [value, index]) -> lowerStringIntBinary context source I32 "vr_runtime_strsub_utf8" value index
      ("strsuffix", [value, index]) -> lowerStringIntBinary context source Ptr "vr_runtime_strsuffix" value index
      ("strsuffixUtf8", [value, index]) -> lowerStringIntBinary context source Ptr "vr_runtime_strsuffix_utf8" value index
      ("substring", [value, start, wantedLength]) -> lowerSubstring context source value start wantedLength
      ("strindex", [value, character]) -> lowerStringIndex context source value character
      ("strsindex", [value, needle]) -> lowerStringsIndex context source value needle
      ("strcspn", [value, characters]) -> lowerStringPair context source I64 "vr_runtime_strcspn" value characters
      ("strchr", [value, character]) -> lowerStringCharacterOption context source value character
      ("currentUrl", []) -> emitResult Ptr "call ptr @vr_runtime_current_url()"
      ("currentUrlHasPost", []) -> emitResult I1 "call i1 @vr_runtime_current_url_has_post()"
      ("currentUrlHasQueryString", []) ->
        emitResult I1 "call i1 @vr_runtime_current_url_has_query_string()"
      ("anchorUrl", [anchor]) -> do
        anchor' <- force context anchor
        ensureOperand source Ptr anchor'
        current <- emitResult Ptr "call ptr @vr_runtime_current_url()"
        withHash <- lowerStringConcatOperands source current
          (stringOperand context (ByteString8.pack "#"))
        lowerStringConcatOperands source withHash anchor'
      ("fresh", []) -> emitResult Ptr "call ptr @vr_runtime_fresh_id()"
      ("url", [value]) -> deferredExpression source value >>= lowerUrlValue context source
      ("effectfulUrl", [value]) -> deferredExpression source value >>= lowerUrlValue context source
      ("null", []) -> pure (stringOperand context ByteString.empty)
      ("noStyle", []) -> pure (stringOperand context ByteString.empty)
      ("join", [left, right]) -> do
        left' <- force context left
        right' <- force context right
        lowerStringConcatOperands source left' right'
      ("tag", tagArguments) -> lowerHtmlTag context source tagArguments
      ("__vr_tag_open", tagArguments) -> do
        lowerOrdinaryHtmlTag context source False
          (tagArguments <> [DeferredExpr (Located (locatedSpan source)
            (M.EPrim (PrimString HtmlString ByteString.empty)))])
      ("getCookie", [cookie]) -> do
        cookie' <- force context cookie
        ensureOperand source Ptr cookie'
        elementSourceType <- staticResultMonoType source staticArguments
        elementType <- liftEither (lowerTypeAt (locatedSpan source) elementSourceType)
        lowerCookieGetter context source elementSourceType elementType cookie'
      ("get_cookie", [cookie]) -> do
        cookie' <- force context cookie
        ensureOperand source Ptr cookie'
        emitResult Ptr ("call ptr @vr_runtime_get_cookie(" <> typed cookie' <> ")")
      ("setCookie", [cookie, settings]) -> do
        cookie' <- force context cookie
        settings' <- force context settings
        ensureOperand source Ptr cookie'
        lowerCookieSetter context source staticArguments cookie' settings'
      ("clearCookie", [cookie]) -> do
        cookie' <- force context cookie
        ensureOperand source Ptr cookie'
        lowerCookieClearer context source cookie'
      ("set_cookie", [path, cookie, serialized, expires, secure]) -> do
        path' <- force context path
        cookie' <- force context cookie
        serialized' <- force context serialized
        expires' <- force context expires
        secure' <- force context secure
        ensureOperand source Ptr path'
        ensureOperand source Ptr cookie'
        ensureOperand source Ptr serialized'
        ensureOperand source Ptr expires'
        ensureOperand source I1 secure'
        emitInstruction
          ("call void @vr_runtime_set_cookie(" <> typed path' <> ", " <> typed cookie' <> ", "
            <> typed serialized' <> ", " <> typed expires' <> ", " <> typed secure' <> ")")
        pure (Operand I8 "0")
      ("clear_cookie", [path, cookie]) -> do
        path' <- force context path
        cookie' <- force context cookie
        ensureOperand source Ptr path'
        ensureOperand source Ptr cookie'
        emitInstruction ("call void @vr_runtime_clear_cookie(" <> typed path' <> ", " <> typed cookie' <> ")")
        pure (Operand I8 "0")
      ("urlifyInt", [value]) -> lowerUrlifyIntrinsic context source I64 "vr_runtime_urlify_int" value
      ("urlifyFloat", [value]) -> lowerUrlifyIntrinsic context source F64 "vr_runtime_urlify_float" value
      ("urlifyString", [value]) -> lowerUrlifyIntrinsic context source Ptr "vr_runtime_urlify_string" value
      ("urlifyBool", [value]) -> lowerUrlifyIntrinsic context source I1 "vr_runtime_urlify_bool" value
      ("urlifyChar", [value]) -> lowerUrlifyIntrinsic context source I32 "vr_runtime_urlify_char" value
      ("urlifyTime", [value]) -> lowerUrlifyIntrinsic context source Ptr "vr_runtime_urlify_time" value
      ("urlifyForeign", [value]) -> case staticArguments of
        M.StaticFfi codecModule codecType [] : _
          | Set.member (codecModule, codecType) (moduleForeignCodecs context) -> do
              value' <- force context value
              ensureOperand source Ptr value'
              runtimeContext <- emitResult Ptr "call ptr @vr_runtime_current_context()"
              emitResult Ptr
                ("call ptr @" <> foreignCodecEncodeSymbol codecModule codecType <> "("
                  <> typed runtimeContext <> ", " <> typed value' <> ")")
        _ -> failCodegen source "llvm-url-codec"
          "Foreign URL serialization is missing a declared clientToServer codec"
      ("textBlob", [value]) -> lowerUnaryPtrRuntime context source "vr_runtime_text_blob" value
      ("textOfBlob", [value]) -> do
        blob <- force context value
        ensureOperand source Ptr blob
        text' <- emitResult Ptr ("call ptr @vr_runtime_text_of_blob(" <> typed blob <> ")")
        lowerMaybeString context source text'
      ("blobSize", [value]) -> do
        blob <- force context value
        ensureOperand source Ptr blob
        emitResult I64 ("call i64 @vr_runtime_blob_size(" <> typed blob <> ")")
      (capability, [value]) | Just (kind, fatal) <- capabilityOperation capability -> do
        value' <- force context value
        ensureOperand source Ptr value'
        checked <- emitResult Ptr
          ("call ptr @vr_runtime_check_capability(" <> typed (stringOperand context (ByteString8.pack kind))
            <> ", " <> typed value' <> ", i1 " <> llvmBool fatal <> ")")
        if fatal
          then pure checked
          else lowerMaybeString context source checked
      ("getHeader", [headerName]) -> do
        name' <- force context headerName
        ensureOperand source Ptr name'
        makeUnitClosure context source "get_header" Ptr [name'] $ \captures -> case captures of
          [capturedName] -> do
            value <- emitResult Ptr ("call ptr @vr_runtime_get_header(" <> typed capturedName <> ")")
            lowerMaybeString context source value
          _ -> failCodegen source "llvm-header" "Internal request-header capture mismatch"
      ("setHeader", [headerName, value]) -> do
        name' <- force context headerName
        value' <- force context value
        ensureOperand source Ptr name'
        ensureOperand source Ptr value'
        makeUnitClosure context source "set_header" I8 [name', value'] $ \captures -> case captures of
          [capturedName, capturedValue] -> do
            emitInstruction ("call void @vr_runtime_set_header(" <> typed capturedName <> ", " <> typed capturedValue <> ")")
            pure (Operand I8 "0")
          _ -> failCodegen source "llvm-header" "Internal response-header capture mismatch"
      ("getenv", [environmentName]) -> do
        name' <- force context environmentName
        ensureOperand source Ptr name'
        makeUnitClosure context source "get_env" Ptr [name'] $ \captures -> case captures of
          [capturedName] -> do
            value <- emitResult Ptr ("call ptr @vr_runtime_get_env(" <> typed capturedName <> ")")
            lowerMaybeString context source value
          _ -> failCodegen source "llvm-env" "Internal environment capture mismatch"
      ("form", [identifier, classes, child]) -> do
        identifier' <- force context identifier
        classes' <- force context classes
        child' <- force context child
        ensureOperand source Ptr identifier'
        ensureOperand source Ptr classes'
        ensureOperand source Ptr child'
        emitResult Ptr
          ("call ptr @vr_runtime_render_form(" <> typed identifier' <> ", " <> typed classes' <> ", " <> typed child' <> ")")
      ("fileName", [file]) -> do
        file' <- force context file
        ensureOperand source Ptr file'
        name' <- emitResult Ptr ("call ptr @vr_runtime_file_name(" <> typed file' <> ")")
        lowerMaybeString context source name'
      ("fileMimeType", [file]) -> lowerUnaryPtrRuntime context source "vr_runtime_file_mime_type" file
      ("fileData", [file]) -> lowerUnaryPtrRuntime context source "vr_runtime_file_data" file
      ("postType", [postBody]) -> lowerUnaryPtrRuntime context source "vr_runtime_post_type" postBody
      ("postData", [postBody]) -> lowerUnaryPtrRuntime context source "vr_runtime_post_data" postBody
      ("firstFormField", [fields]) -> do
        fields' <- force context fields
        ensureOperand source Ptr fields'
        value <- emitResult Ptr ("call ptr @vr_runtime_first_form_field(" <> typed fields' <> ")")
        lowerMaybeString context source value
      ("fieldName", [field]) -> lowerUnaryPtrRuntime context source "vr_runtime_field_name" field
      ("fieldValue", [field]) -> lowerUnaryPtrRuntime context source "vr_runtime_field_value" field
      ("remainingFields", [field]) -> lowerUnaryPtrRuntime context source "vr_runtime_remaining_fields" field
      (control, [attributes]) | control `elem` serverInputControlNames -> do
        fieldName <- case reverse staticArguments of
          M.StaticName found : _ -> pure found
          _ -> failCodegen source "llvm-form-control" ("Basis." <> control <> " has no resolved field name")
        attributesExpression <- deferredExpression source attributes
        renderedAttributes <- lowerHtmlAttributes context source Nothing attributesExpression
        let inputType = htmlInputType control
        emitResult Ptr
          ("call ptr @vr_runtime_render_input("
            <> typed (stringOperand context (ByteString8.pack inputType)) <> ", "
            <> typed (stringOperand context (ByteString8.pack fieldName)) <> ", "
            <> typed renderedAttributes <> ")")
      ("neg", [_dictionary, value]) -> do
        value' <- force context value
        case operandType value' of
          I64 -> emitResult I64 ("sub i64 0, " <> operandText value')
          F64 -> emitResult F64 ("fneg double " <> operandText value')
          _ -> failCodegen source "llvm-numeric-type" ("Numeric negation received " <> renderType (operandType value'))
      (operator, [_dictionary, left, right]) | operator `elem` ["plus", "minus", "times", "div", "divide", "mod", "pow"] -> do
        left' <- force context left
        right' <- force context right
        ensureSame source left' right'
        lowerNumeric source (if operator == "divide" then "div" else operator) left' right'
      (operator, [_dictionary, left, right]) | operator `elem` ["eq", "neq", "lt", "le", "gt", "ge"] -> do
        left' <- force context left
        right' <- force context right
        ensureSame source left' right'
        lowerComparison source staticArguments operator left' right'
      ("strcat", [left, right]) -> do
        left' <- force context left
        right' <- force context right
        lowerStringConcatOperands source left' right'
      _ -> failCodegen source "llvm-basis" ("Unsupported Basis intrinsic or arity: " <> name <> "/" <> show (length arguments))

lowerUrlifyIntrinsic :: ModuleContext -> M.Expr -> LlvmType -> String -> Deferred -> Codegen Operand
lowerUrlifyIntrinsic context source expected function value = do
  value' <- force context value
  ensureOperand source expected value'
  emitResult Ptr ("call ptr @" <> function <> "(" <> typed value' <> ")")

lowerUnaryPtrRuntime :: ModuleContext -> M.Expr -> String -> Deferred -> Codegen Operand
lowerUnaryPtrRuntime context source function value = do
  value' <- force context value
  ensureOperand source Ptr value'
  emitResult Ptr ("call ptr @" <> function <> "(" <> typed value' <> ")")

lowerStringUnary :: ModuleContext -> M.Expr -> LlvmType -> String -> Deferred -> Codegen Operand
lowerStringUnary context source resultType function value = do
  value' <- force context value
  ensureOperand source Ptr value'
  emitResult resultType
    ("call " <> renderType resultType <> " @" <> function <> "(" <> typed value' <> ")")

lowerIntUnary :: ModuleContext -> M.Expr -> LlvmType -> String -> Deferred -> Codegen Operand
lowerIntUnary context source resultType function value = do
  value' <- force context value
  ensureOperand source I64 value'
  emitResult resultType
    ("call " <> renderType resultType <> " @" <> function <> "(" <> typed value' <> ")")

lowerCharUnary :: ModuleContext -> M.Expr -> LlvmType -> String -> Deferred -> Codegen Operand
lowerCharUnary context source resultType function value = do
  value' <- force context value
  ensureOperand source I32 value'
  emitResult resultType
    ("call " <> renderType resultType <> " @" <> function <> "(" <> typed value' <> ")")

lowerFloatUnary :: ModuleContext -> M.Expr -> String -> Deferred -> Codegen Operand
lowerFloatUnary context source function value = do
  value' <- force context value
  ensureOperand source F64 value'
  emitResult F64 ("call double @" <> function <> "(" <> typed value' <> ")")

lowerFloatPair :: ModuleContext -> M.Expr -> String -> Deferred -> Deferred -> Codegen Operand
lowerFloatPair context source function left right = do
  left' <- force context left
  right' <- force context right
  ensureOperand source F64 left'
  ensureOperand source F64 right'
  emitResult F64
    ("call double @" <> function <> "(" <> typed left' <> ", " <> typed right' <> ")")

lowerTimeIntBinary
  :: ModuleContext -> M.Expr -> LlvmType -> String -> Deferred -> Deferred -> Codegen Operand
lowerTimeIntBinary context source resultType function value integer = do
  value' <- force context value
  integer' <- force context integer
  ensureOperand source Ptr value'
  ensureOperand source I64 integer'
  emitResult resultType
    ("call " <> renderType resultType <> " @" <> function
      <> "(" <> typed value' <> ", " <> typed integer' <> ")")

lowerFromDatetime :: ModuleContext -> M.Expr -> [Deferred] -> Codegen Operand
lowerFromDatetime context source values = do
  values' <- mapM (force context) values
  mapM_ (ensureOperand source I64) values'
  emitResult Ptr
    ("call ptr @vr_runtime_from_datetime(" <> intercalate ", " (map typed values') <> ")")

lowerParsedOption :: ModuleContext -> M.Expr -> LlvmType -> String -> Deferred -> Codegen Operand
lowerParsedOption context source resultType function value = do
  value' <- force context value
  ensureOperand source Ptr value'
  parsed <- emitResult Ptr ("call ptr @" <> function <> "(" <> typed value' <> ")")
  missing <- emitResult I1 ("icmp eq ptr " <> operandText parsed <> ", null")
  noneLabel <- freshLabel "read_none"
  someLabel <- freshLabel "read_some"
  mergeLabel <- freshLabel "read_merge"
  emitInstruction ("br i1 " <> operandText missing <> ", label %" <> noneLabel <> ", label %" <> someLabel)
  emitBlock noneLabel
  none <- allocateTagged context source 0 Nothing
  noneBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock someLabel
  decoded <- emitResult resultType ("load " <> renderType resultType <> ", ptr " <> operandText parsed)
  some <- allocateTagged context source 1 (Just decoded)
  someBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock mergeLabel
  emitResult Ptr
    ("phi ptr [ " <> operandText none <> ", %" <> noneBlock <> " ], [ "
      <> operandText some <> ", %" <> someBlock <> " ]")

lowerStringIntBinary
  :: ModuleContext -> M.Expr -> LlvmType -> String -> Deferred -> Deferred -> Codegen Operand
lowerStringIntBinary context source resultType function value index = do
  value' <- force context value
  index' <- force context index
  ensureOperand source Ptr value'
  ensureOperand source I64 index'
  emitResult resultType
    ("call " <> renderType resultType <> " @" <> function <> "(" <> typed value' <> ", " <> typed index' <> ")")

lowerStringPair
  :: ModuleContext -> M.Expr -> LlvmType -> String -> Deferred -> Deferred -> Codegen Operand
lowerStringPair context source resultType function left right = do
  left' <- force context left
  right' <- force context right
  ensureOperand source Ptr left'
  ensureOperand source Ptr right'
  emitResult resultType
    ("call " <> renderType resultType <> " @" <> function <> "(" <> typed left' <> ", " <> typed right' <> ")")

lowerSubstring :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Deferred -> Codegen Operand
lowerSubstring context source value start wantedLength = do
  value' <- force context value
  start' <- force context start
  length' <- force context wantedLength
  ensureOperand source Ptr value'
  ensureOperand source I64 start'
  ensureOperand source I64 length'
  emitResult Ptr
    ("call ptr @vr_runtime_substring(" <> typed value' <> ", " <> typed start' <> ", " <> typed length' <> ")")

lowerStringIndex :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerStringIndex context source value character = do
  value' <- force context value
  character' <- force context character
  ensureOperand source Ptr value'
  ensureOperand source I32 character'
  index <- emitResult I64
    ("call i64 @vr_runtime_strindex(" <> typed value' <> ", " <> typed character' <> ")")
  lowerOptionalIndex context source index

lowerStringsIndex :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerStringsIndex context source value needle = do
  value' <- force context value
  needle' <- force context needle
  ensureOperand source Ptr value'
  ensureOperand source Ptr needle'
  index <- emitResult I64
    ("call i64 @vr_runtime_strsindex(" <> typed value' <> ", " <> typed needle' <> ")")
  lowerOptionalIndex context source index

lowerOptionalIndex :: ModuleContext -> M.Expr -> Operand -> Codegen Operand
lowerOptionalIndex context source index = do
  missing <- emitResult I1 ("icmp slt i64 " <> operandText index <> ", 0")
  noneLabel <- freshLabel "string_index_none"
  someLabel <- freshLabel "string_index_some"
  mergeLabel <- freshLabel "string_index_merge"
  emitInstruction ("br i1 " <> operandText missing <> ", label %" <> noneLabel <> ", label %" <> someLabel)
  emitBlock noneLabel
  none <- allocateTagged context source 0 Nothing
  noneBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock someLabel
  some <- allocateTagged context source 1 (Just index)
  someBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock mergeLabel
  emitResult Ptr
    ("phi ptr [ " <> operandText none <> ", %" <> noneBlock <> " ], [ "
      <> operandText some <> ", %" <> someBlock <> " ]")

lowerStringCharacterOption :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerStringCharacterOption context source value character = do
  value' <- force context value
  character' <- force context character
  ensureOperand source Ptr value'
  ensureOperand source I32 character'
  suffix <- emitResult Ptr
    ("call ptr @vr_runtime_strchr(" <> typed value' <> ", " <> typed character' <> ")")
  lowerMaybeString context source suffix

capabilityOperation :: String -> Maybe (String, Bool)
capabilityOperation name = case name of
  "bless" -> Just ("url", True)
  "checkUrl" -> Just ("url", False)
  "blessMime" -> Just ("mime", True)
  "checkMime" -> Just ("mime", False)
  "blessRequestHeader" -> Just ("requestHeader", True)
  "checkRequestHeader" -> Just ("requestHeader", False)
  "blessResponseHeader" -> Just ("responseHeader", True)
  "checkResponseHeader" -> Just ("responseHeader", False)
  "blessEnvVar" -> Just ("env", True)
  "checkEnvVar" -> Just ("env", False)
  "blessMeta" -> Just ("meta", True)
  "checkMeta" -> Just ("meta", False)
  "blessData" -> Just ("data", True)
  _ -> Nothing

lowerMaybeString :: ModuleContext -> M.Expr -> Operand -> Codegen Operand
lowerMaybeString context source value = do
  missing <- emitResult I1 ("icmp eq ptr " <> operandText value <> ", null")
  noneLabel <- freshLabel "maybe_none"
  someLabel <- freshLabel "maybe_some"
  mergeLabel <- freshLabel "maybe_merge"
  emitInstruction ("br i1 " <> operandText missing <> ", label %" <> noneLabel <> ", label %" <> someLabel)
  emitBlock noneLabel
  none <- allocateTagged context source 0 Nothing
  noneBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock someLabel
  some <- allocateTagged context source 1 (Just value)
  someBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock mergeLabel
  emitResult Ptr
    ("phi ptr [ " <> operandText none <> ", %" <> noneBlock <> " ], [ "
      <> operandText some <> ", %" <> someBlock <> " ]")

lowerCookieGetter
  :: ModuleContext -> M.Expr -> M.Type -> LlvmType -> Operand -> Codegen Operand
lowerCookieGetter context source elementSourceType elementType cookie =
  makeUnitClosure context source "get_cookie" Ptr [cookie] $ \captures -> case captures of
    [cookie'] -> do
      serialized <- emitResult Ptr ("call ptr @vr_runtime_get_cookie(" <> typed cookie' <> ")")
      missing <- emitResult I1 ("icmp eq ptr " <> operandText serialized <> ", null")
      noneLabel <- freshLabel "cookie_none"
      someLabel <- freshLabel "cookie_some"
      mergeLabel <- freshLabel "cookie_merge"
      emitInstruction ("br i1 " <> operandText missing <> ", label %" <> noneLabel <> ", label %" <> someLabel)
      emitBlock noneLabel
      none <- allocateTagged context source 0 Nothing
      noneBlock <- gets codegenCurrentBlock
      emitInstruction ("br label %" <> mergeLabel)
      emitBlock someLabel
      emitInstruction ("call void @vr_runtime_unurlify_begin(" <> typed serialized <> ")")
      value <- lowerComponentDecodeNext context source
        "vr_runtime_next_unurlify_component" Map.empty elementSourceType elementType
      emitInstruction "call void @vr_runtime_require_unurlify_done()"
      some <- allocateTagged context source 1 (Just value)
      someBlock <- gets codegenCurrentBlock
      emitInstruction ("br label %" <> mergeLabel)
      emitBlock mergeLabel
      emitResult Ptr
        ("phi ptr [ " <> operandText none <> ", %" <> noneBlock <> " ], [ "
          <> operandText some <> ", %" <> someBlock <> " ]")
    _ -> failCodegen source "llvm-cookie" "Internal cookie getter capture mismatch"

lowerCookieSetter :: ModuleContext -> M.Expr -> [M.StaticArg] -> Operand -> Operand -> Codegen Operand
lowerCookieSetter context source staticArguments cookie settings = do
  elementSourceType <- staticResultMonoType source staticArguments
  elementType <- liftEither (lowerTypeAt (locatedSpan source) elementSourceType)
  case operandType settings of
    Record fields -> do
      valueIndex <- requiredField "Value" fields
      expiresIndex <- requiredField "Expires" fields
      secureIndex <- requiredField "Secure" fields
      makeUnitClosure context source "set_cookie" I8 [cookie, settings] $ \captures -> case captures of
        [cookie', settings'] -> do
          value <- extractValue settings' valueIndex elementType
          expires <- extractValue settings' expiresIndex Ptr
          secure <- extractValue settings' secureIndex I1
          serialized <- lowerUrlEncode context source elementSourceType value
          let path = stringOperand context (ByteString8.pack "/")
          emitInstruction
            ("call void @vr_runtime_set_cookie(" <> typed path <> ", " <> typed cookie' <> ", "
              <> typed serialized <> ", " <> typed expires <> ", " <> typed secure <> ")")
          pure (Operand I8 "0")
        _ -> failCodegen source "llvm-cookie" "Internal cookie setter capture mismatch"
    _ -> failCodegen source "llvm-cookie-settings" "Cookie settings did not lower to a concrete record"
  where
    requiredField name fields = case lookupField name fields of
      Just found -> pure found
      Nothing -> failCodegen source "llvm-cookie-settings" ("Cookie settings are missing field " <> name)
    extractValue aggregate (index, expected) actual = do
      if expected == actual then pure () else failCodegen source "llvm-cookie-settings" "Cookie setting has an unexpected type"
      emitResult actual ("extractvalue " <> renderType (operandType aggregate) <> " " <> operandText aggregate <> ", " <> show index)

lowerCookieClearer :: ModuleContext -> M.Expr -> Operand -> Codegen Operand
lowerCookieClearer context source cookie =
  makeUnitClosure context source "clear_cookie" I8 [cookie] $ \captures -> case captures of
    [cookie'] -> do
      let path = stringOperand context (ByteString8.pack "/")
      emitInstruction ("call void @vr_runtime_clear_cookie(" <> typed path <> ", " <> typed cookie' <> ")")
      pure (Operand I8 "0")
    _ -> failCodegen source "llvm-cookie" "Internal cookie clearer capture mismatch"

makeUnitClosure
  :: ModuleContext
  -> M.Expr
  -> String
  -> LlvmType
  -> [Operand]
  -> ([Operand] -> Codegen Operand)
  -> Codegen Operand
makeUnitClosure _context source purpose range captures build = do
  helperName <- freshHelperName purpose
  environment <- allocateEnvironment captures
  let helperInitial = initialCodegenState helperName []
      buildHelper = do
        restored <- restoreEnvironment captures
        build restored
  (result, helperFinal) <- liftEither (runStateT buildHelper helperInitial)
  ensureOperand source range result
  addHelperDefinition helperName I8 range result helperFinal
  allocateClosure helperName (Function I8 range) environment Nothing

-- Build a unit closure whose body is lowered in the helper itself.  This is
-- necessary when the body may create nested closures: lowering it before the
-- helper would make those closures refer to registers from the wrong LLVM
-- function.  The complete lexical environment is restored before the body is
-- visited, preserving Mono's de Bruijn indices.
makeScopedUnitClosure
  :: M.Expr
  -> String
  -> LlvmType
  -> Codegen Operand
  -> Codegen Operand
makeScopedUnitClosure source purpose range build = do
  locals <- gets codegenLocals
  helperName <- freshHelperName purpose
  environment <- allocateEnvironment locals
  let helperInitial = initialCodegenState helperName []
      buildHelper = do
        restored <- restoreEnvironment locals
        modify' (\state -> state {codegenLocals = restored})
        build
  (result, helperFinal) <- liftEither (runStateT buildHelper helperInitial)
  ensureOperand source range result
  addHelperDefinition helperName I8 range result helperFinal
  allocateClosure helperName (Function I8 range) environment Nothing

makeUnaryClosure
  :: M.Expr
  -> String
  -> LlvmType
  -> LlvmType
  -> [Operand]
  -> ([Operand] -> Operand -> Codegen Operand)
  -> Codegen Operand
makeUnaryClosure source purpose domain range captures build = do
  helperName <- freshHelperName purpose
  environment <- allocateEnvironment captures
  let helperInitial = initialCodegenState helperName []
      buildHelper = do
        restored <- restoreEnvironment captures
        build restored (Operand domain "%argument")
  (result, helperFinal) <- liftEither (runStateT buildHelper helperInitial)
  ensureOperand source range result
  addHelperDefinition helperName domain range result helperFinal
  allocateClosure helperName (Function domain range) environment Nothing

makeSqlRuntimeEncoder :: M.Expr -> String -> LlvmType -> String -> Codegen Operand
makeSqlRuntimeEncoder source purpose domain function =
  makeUnaryClosure source purpose domain Ptr [] $ \_ argument ->
    emitResult Ptr ("call ptr @" <> function <> "(" <> typed argument <> ")")

lowerSqlOption
  :: ModuleContext
  -> M.Expr
  -> LlvmType
  -> Operand
  -> Operand
  -> Codegen Operand
lowerSqlOption context source elementType encoder option = do
  ensureOperand source Ptr option
  tagAddress <- emitResult Ptr
    ("getelementptr inbounds { i32, ptr }, ptr " <> operandText option <> ", i32 0, i32 0")
  tag <- emitResult I32 ("load i32, ptr " <> operandText tagAddress)
  isNone <- emitResult I1 ("icmp eq i32 " <> operandText tag <> ", 0")
  noneLabel <- freshLabel "sql_none"
  someLabel <- freshLabel "sql_some"
  mergeLabel <- freshLabel "sql_option_merge"
  emitInstruction ("br i1 " <> operandText isNone <> ", label %" <> noneLabel <> ", label %" <> someLabel)
  emitBlock noneLabel
  let none = stringOperand context (ByteString8.pack "NULL")
  noneBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock someLabel
  payloadAddressField <- emitResult Ptr
    ("getelementptr inbounds { i32, ptr }, ptr " <> operandText option <> ", i32 0, i32 1")
  payloadAddress <- emitResult Ptr ("load ptr, ptr " <> operandText payloadAddressField)
  payload <- emitResult elementType
    ("load " <> renderType elementType <> ", ptr " <> operandText payloadAddress)
  some <- applyClosure context source encoder (Lowered payload)
  ensureOperand source Ptr some
  someBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock mergeLabel
  emitResult Ptr
    ("phi ptr [ " <> operandText none <> ", %" <> noneBlock <> " ], [ "
      <> operandText some <> ", %" <> someBlock <> " ]")

lowerSqlInsert
  :: ModuleContext
  -> M.Expr
  -> [M.StaticArg]
  -> Deferred
  -> Deferred
  -> Codegen Operand
lowerSqlInsert context source _staticArguments table fields = do
  table' <- force context table
  fields' <- force context fields
  ensureOperand source Ptr table'
  prefixed <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "INSERT INTO ")) table'
  case operandType fields' of
    Record [] -> lowerStringConcatOperands source prefixed
      (stringOperand context (ByteString8.pack " DEFAULT VALUES"))
    recordType@(Record described) -> do
      names <- joinSqlPieces context source
        [stringOperand context (ByteString8.pack (sqlColumnIdentifier context name)) | (name, _) <- described]
      values <- forM (zip [0 :: Int ..] described) $ \(index, (_, typ)) -> do
        value <- emitResult typ
          ("extractvalue " <> renderType recordType <> " " <> operandText fields' <> ", " <> show index)
        ensureOperand source Ptr value
        pure value
      encodedValues <- joinSqlPieces context source values
      withOpen <- lowerStringConcatOperands source prefixed
        (stringOperand context (ByteString8.pack " ("))
      withNames <- lowerStringConcatOperands source withOpen names
      withValuesPrefix <- lowerStringConcatOperands source withNames
        (stringOperand context (ByteString8.pack ") VALUES ("))
      withValues <- lowerStringConcatOperands source withValuesPrefix encodedValues
      lowerStringConcatOperands source withValues (stringOperand context (ByteString8.pack ")"))
    actual -> failCodegen source "llvm-insert"
      ("SQL insert fields received " <> renderType actual)

joinSqlPieces :: ModuleContext -> M.Expr -> [Operand] -> Codegen Operand
joinSqlPieces context _ [] = pure (stringOperand context ByteString.empty)
joinSqlPieces _ source (first : rest) = foldM append first rest
  where
    append combined next = do
      mapM_ (ensureOperand source Ptr) [combined, next]
      emitResult Ptr
        ("call ptr @vr_runtime_sql_comma(" <> typed combined <> ", " <> typed next <> ")")

lowerTryDml :: ModuleContext -> M.Expr -> Operand -> Codegen Operand
lowerTryDml context source command = do
  errorMessage <- emitResult Ptr
    ("call ptr @vr_runtime_database_try_exec(" <> typed command <> ")")
  lowerMaybeString context source errorMessage

lowerPrimaryKey :: ModuleContext -> M.Expr -> [M.StaticArg] -> Codegen Operand
lowerPrimaryKey context source staticArguments =
  joinSqlPieces context source
    (map (stringOperand context . ByteString8.pack) (schemaKeyColumns context staticArguments))

lowerUnique :: ModuleContext -> M.Expr -> [M.StaticArg] -> Codegen Operand
lowerUnique context source staticArguments = do
  columns <- joinSqlPieces context source
    (map (stringOperand context . ByteString8.pack) (schemaKeyColumns context staticArguments))
  opened <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "UNIQUE (")) columns
  lowerStringConcatOperands source opened
    (stringOperand context (ByteString8.pack ")"))

schemaKeyNames :: [M.StaticArg] -> [String]
schemaKeyNames = map fst . schemaKeyFields

schemaKeyColumns :: ModuleContext -> [M.StaticArg] -> [String]
schemaKeyColumns context = map render . schemaKeyFields
  where
    render (name, typ) = sqlColumnIdentifier context name
      <> if moduleDatabaseSystem context == DatabaseMySQL && staticSqlTextType typ
           then "(255)"
           else ""

schemaKeyFields :: [M.StaticArg] -> [(String, M.StaticArg)]
schemaKeyFields arguments = case reverse [name | M.StaticName name <- arguments] of
  [] -> []
  first : _ -> (first, firstType) : case reverse [fields | M.StaticRow fields <- arguments] of
    fields : _ -> [(name, typ) | (M.StaticName name, typ) <- fields]
    [] -> []
  where
    firstType = case reverse
      [typ | typ@M.StaticFfi {} <- arguments] <> reverse
      [typ | typ@M.StaticType {} <- arguments] of
        typ : _ -> typ
        [] -> M.StaticUnit

staticSqlTextType :: M.StaticArg -> Bool
staticSqlTextType argument = case argument of
  M.StaticType typ -> sqlTextType typ
  M.StaticFfi "Basis" "string" _ -> True
  M.StaticFfi "Basis" "option" nested -> any staticSqlTextType nested
  _ -> False

lowerOneConstraint
  :: ModuleContext -> M.Expr -> [M.StaticArg] -> Deferred -> Codegen Operand
lowerOneConstraint context source staticArguments constraint = do
  constraint' <- force context constraint
  ensureOperand source Ptr constraint'
  case reverse [name | M.StaticName name <- staticArguments] of
    name : _ -> buildRecordOperand source [(name, constraint')]
    [] -> failCodegen source "llvm-table-schema" "Named constraint has no resolved name"

lowerConstraintJoin
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerConstraintJoin context source left right = do
  left' <- force context left
  right' <- force context right
  concatRecordOperands source left' right'

concatRecordOperands :: M.Expr -> Operand -> Operand -> Codegen Operand
concatRecordOperands source left right = case (operandType left, operandType right) of
  (I8, I8) -> pure (Operand I8 "0")
  (I8, Record {}) -> pure right
  (Record {}, I8) -> pure left
  (Record leftFields, Record rightFields) -> do
    let resultType = Record (leftFields <> rightFields)
    afterLeft <- copyRecordFields resultType 0 left (Operand resultType "undef")
    copyRecordFields resultType (length leftFields) right afterLeft
  _ -> failCodegen source "llvm-table-schema" "Constraint concatenation received a non-record operand"

lowerMatchingNil :: ModuleContext -> M.Expr -> Codegen Operand
lowerMatchingNil context source = buildRecordOperand source
  [ ("1", stringOperand context ByteString.empty)
  , ("2", stringOperand context ByteString.empty)
  ]

lowerMatchingCons
  :: ModuleContext -> M.Expr -> [M.StaticArg] -> Deferred -> Codegen Operand
lowerMatchingCons context source staticArguments matching = do
  matching' <- force context matching
  mine <- extractRecordOperandField source matching' "1"
  foreignFields <- extractRecordOperandField source matching' "2"
  case reverse [name | M.StaticName name <- staticArguments] of
    foreignName : mineName : _ -> do
      mine' <- emitResult Ptr
        ("call ptr @vr_runtime_sql_comma("
          <> typed (stringOperand context (ByteString8.pack (sqlColumnIdentifier context mineName))) <> ", " <> typed mine <> ")")
      foreign' <- emitResult Ptr
        ("call ptr @vr_runtime_sql_comma("
          <> typed (stringOperand context (ByteString8.pack (sqlColumnIdentifier context foreignName))) <> ", " <> typed foreignFields <> ")")
      buildRecordOperand source [("1", mine'), ("2", foreign')]
    _ -> failCodegen source "llvm-table-schema" "Foreign-key matching has no resolved field names"

lowerForeignKey
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Deferred -> Codegen Operand
lowerForeignKey context source matching table properties = do
  matching' <- force context matching
  table' <- force context table
  properties' <- force context properties
  mine <- extractRecordOperandField source matching' "1"
  foreignFields <- extractRecordOperandField source matching' "2"
  onDelete <- extractRecordOperandField source properties' "OnDelete"
  onUpdate <- extractRecordOperandField source properties' "OnUpdate"
  mapM_ (ensureOperand source Ptr) [mine, foreignFields, table', onDelete, onUpdate]
  opened <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "FOREIGN KEY (")) mine
  withReference <- lowerStringConcatOperands source opened
    (stringOperand context (ByteString8.pack ") REFERENCES "))
  withTable <- lowerStringConcatOperands source withReference table'
  withOpen <- lowerStringConcatOperands source withTable
    (stringOperand context (ByteString8.pack " ("))
  withForeign <- lowerStringConcatOperands source withOpen foreignFields
  closed <- lowerStringConcatOperands source withForeign
    (stringOperand context (ByteString8.pack ")"))
  deleteClause <- lowerPropagationClause context source " ON DELETE " onDelete
  updateClause <- lowerPropagationClause context source " ON UPDATE " onUpdate
  withDelete <- lowerStringConcatOperands source closed deleteClause
  lowerStringConcatOperands source withDelete updateClause

lowerPropagationClause
  :: ModuleContext -> M.Expr -> String -> Operand -> Codegen Operand
lowerPropagationClause context source prefix value = do
  comparison <- emitResult I32
    ("call i32 @strcmp(" <> typed value <> ", "
      <> typed (stringOperand context (ByteString8.pack "NO ACTION")) <> ")")
  explicit <- emitResult I1 ("icmp ne i32 " <> operandText comparison <> ", 0")
  explicitLabel <- freshLabel "constraint_propagation"
  defaultLabel <- freshLabel "constraint_no_action"
  mergeLabel <- freshLabel "constraint_propagation_merge"
  emitInstruction ("br i1 " <> operandText explicit <> ", label %" <> explicitLabel <> ", label %" <> defaultLabel)
  emitBlock explicitLabel
  clause <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack prefix)) value
  clauseBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock defaultLabel
  let empty = stringOperand context ByteString.empty
  emptyBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock mergeLabel
  emitResult Ptr
    ("phi ptr [ " <> operandText clause <> ", %" <> clauseBlock <> " ], [ "
      <> operandText empty <> ", %" <> emptyBlock <> " ]")

lowerCheckConstraint :: ModuleContext -> M.Expr -> Deferred -> Codegen Operand
lowerCheckConstraint context source expression = do
  expression' <- force context expression
  ensureOperand source Ptr expression'
  lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "CHECK ")) expression'

sqlOperatorText :: String -> Maybe String
sqlOperatorText name = lookup name
  [ ("sql_not", "NOT"), ("sql_neg", "-")
  , ("sql_and", "AND"), ("sql_or", "OR")
  , ("sql_plus", "+"), ("sql_minus", "-"), ("sql_times", "*")
  , ("sql_div", "/"), ("sql_mod", "%")
  , ("sql_eq", "="), ("sql_ne", "<>")
  , ("sql_lt", "<"), ("sql_le", "<="), ("sql_gt", ">"), ("sql_ge", ">=")
  , ("sql_like", "LIKE")
  ]

lowerSqlField :: ModuleContext -> M.Expr -> [M.StaticArg] -> Codegen Operand
lowerSqlField context source staticArguments = case [name | M.StaticName name <- staticArguments] of
  names | length names >= 2 -> do
    let table = names !! (length names - 2)
        field = last names
    withTable <- lowerStringConcatOperands source
      (stringOperand context (ByteString8.pack "T_"))
      (stringOperand context (ByteString8.pack table))
    withDot <- lowerStringConcatOperands source withTable
      (stringOperand context (ByteString8.pack "."))
    lowerStringConcatOperands source withDot
      (stringOperand context (ByteString8.pack (sqlColumnIdentifier context field)))
  _ -> failCodegen source "llvm-sql-field" "SQL field reference has no resolved table and field names"

lowerSqlIsNull :: ModuleContext -> M.Expr -> Deferred -> Codegen Operand
lowerSqlIsNull context source value = do
  value' <- force context value
  ensureOperand source Ptr value'
  opened <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "(")) value'
  lowerStringConcatOperands source opened
    (stringOperand context (ByteString8.pack " IS NULL)"))

lowerSqlCall2
  :: ModuleContext -> M.Expr -> String -> Deferred -> Deferred -> Codegen Operand
lowerSqlCall2 context source prefix left right = do
  left' <- force context left
  right' <- force context right
  mapM_ (ensureOperand source Ptr) [left', right']
  opened <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack prefix)) left'
  separated <- lowerStringConcatOperands source opened
    (stringOperand context (ByteString8.pack ", "))
  withRight <- lowerStringConcatOperands source separated right'
  lowerStringConcatOperands source withRight
    (stringOperand context (ByteString8.pack ")"))

lowerSqlCall1
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerSqlCall1 context source function value = do
  function' <- force context function
  value' <- force context value
  mapM_ (ensureOperand source Ptr) [function', value']
  opened <- lowerStringConcatOperands source function'
    (stringOperand context (ByteString8.pack "("))
  withValue <- lowerStringConcatOperands source opened value'
  lowerStringConcatOperands source withValue
    (stringOperand context (ByteString8.pack ")"))

lowerSqlNamedCall2
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Deferred -> Codegen Operand
lowerSqlNamedCall2 context source function left right = do
  function' <- force context function
  left' <- force context left
  right' <- force context right
  mapM_ (ensureOperand source Ptr) [function', left', right']
  opened <- lowerStringConcatOperands source function'
    (stringOperand context (ByteString8.pack "("))
  withLeft <- lowerStringConcatOperands source opened left'
  separated <- lowerStringConcatOperands source withLeft
    (stringOperand context (ByteString8.pack ","))
  withRight <- lowerStringConcatOperands source separated right'
  lowerStringConcatOperands source withRight
    (stringOperand context (ByteString8.pack ")"))

lowerSqlPartition :: ModuleContext -> M.Expr -> Deferred -> Codegen Operand
lowerSqlPartition context source expression = do
  expression' <- force context expression
  ensureOperand source Ptr expression'
  lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "PARTITION BY ")) expression'

lowerSqlWindowFunction
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Deferred -> Codegen Operand
lowerSqlWindowFunction context source window partition order = do
  window' <- force context window
  partition' <- force context partition
  order' <- force context order
  mapM_ (ensureOperand source Ptr) [window', partition', order']
  opened <- lowerStringConcatOperands source window'
    (stringOperand context (ByteString8.pack " OVER ("))
  withPartition <- lowerStringConcatOperands source opened partition'
  orderClause <- emitResult Ptr
    ("call ptr @vr_runtime_sql_clause("
      <> typed (stringOperand context (ByteString8.pack " ORDER BY ")) <> ", "
      <> typed order' <> ", i1 false)")
  withOrder <- lowerStringConcatOperands source withPartition orderClause
  lowerStringConcatOperands source withOrder
    (stringOperand context (ByteString8.pack ")"))

lowerPolymorphicVariantMake
  :: ModuleContext -> M.Expr -> [M.StaticArg] -> Deferred -> Codegen Operand
lowerPolymorphicVariantMake context source staticArguments value = case staticArguments of
  M.StaticName name : payloadType : M.StaticRow remaining : _ -> do
    value' <- force context value
    expected <- liftEither (lowerStaticTypeAt (locatedSpan source) payloadType)
    ensureOperand source expected value'
    let variants = sortOn fst
          ((name, payloadType) : [(field, typ) | (M.StaticName field, typ) <- remaining])
    tag <- case lookup name (zip (map fst variants) [0 :: Int ..]) of
      Just found -> pure found
      Nothing -> failCodegen source "llvm-polymorphic-variant"
        ("Polymorphic variant has no tag " <> name)
    allocateTagged context source tag (Just value')
  _ -> failCodegen source "llvm-polymorphic-variant"
    "Basis.make is missing its resolved variant name or row"

lowerPolymorphicVariantMatch
  :: ModuleContext -> M.Expr -> [M.StaticArg] -> Deferred -> Deferred -> Codegen Operand
lowerPolymorphicVariantMatch context source staticArguments variant handlers = case staticArguments of
  M.StaticRow row : resultShape : _ -> do
    variant' <- force context variant
    handlers' <- force context handlers
    ensureOperand source Ptr variant'
    resultType <- liftEither (lowerStaticTypeAt (locatedSpan source) resultShape)
    describedHandlers <- case operandType handlers' of
      Record fields -> pure fields
      actual -> failCodegen source "llvm-polymorphic-variant"
        ("Basis.match handlers received " <> renderType actual)
    let variants = sortOn fst [(name, typ) | (M.StaticName name, typ) <- row]
    tagAddress <- emitResult Ptr
      ("getelementptr inbounds { i32, ptr }, ptr " <> operandText variant' <> ", i32 0, i32 0")
    tag <- emitResult I32 ("load i32, ptr " <> operandText tagAddress)
    payloadAddressField <- emitResult Ptr
      ("getelementptr inbounds { i32, ptr }, ptr " <> operandText variant' <> ", i32 0, i32 1")
    payloadAddress <- emitResult Ptr ("load ptr, ptr " <> operandText payloadAddressField)
    testLabels <- mapM (const (freshLabel "pvar_test")) variants
    bodyLabels <- mapM (const (freshLabel "pvar_body")) variants
    failureLabel <- freshLabel "pvar_failure"
    mergeLabel <- freshLabel "pvar_merge"
    case testLabels of
      first : _ -> emitInstruction ("br label %" <> first)
      [] -> failCodegen source "llvm-polymorphic-variant" "Basis.match received an empty variant row"
    incoming <- forM (zip4 (zip [0 :: Int ..] variants) testLabels bodyLabels
      (drop 1 testLabels <> [failureLabel])) $
      \((expectedTag, (name, payloadShape)), testLabel, bodyLabel, nextLabel) -> do
        emitBlock testLabel
        matches <- emitResult I1
          ("icmp eq i32 " <> operandText tag <> ", " <> show expectedTag)
        emitInstruction
          ("br i1 " <> operandText matches <> ", label %" <> bodyLabel <> ", label %" <> nextLabel)
        emitBlock bodyLabel
        (handlerIndex, handlerType) <- case lookupField name describedHandlers of
          Just found -> pure found
          Nothing -> failCodegen source "llvm-polymorphic-variant"
            ("Basis.match has no handler for tag " <> name)
        payloadType <- liftEither (lowerStaticTypeAt (locatedSpan source) payloadShape)
        handler <- emitResult handlerType
          ("extractvalue " <> renderType (operandType handlers') <> " "
            <> operandText handlers' <> ", " <> show handlerIndex)
        payload <- emitResult payloadType
          ("load " <> renderType payloadType <> ", ptr " <> operandText payloadAddress)
        result <- applyClosure context source handler (Lowered payload)
        ensureOperand source resultType result
        predecessor <- gets codegenCurrentBlock
        emitInstruction ("br label %" <> mergeLabel)
        pure (result, predecessor)
    emitBlock failureLabel
    emitInstruction "call void @llvm.trap()"
    emitInstruction "unreachable"
    emitBlock mergeLabel
    emitResult resultType
      ("phi " <> renderType resultType <> " " <> intercalate ", "
        ["[ " <> operandText result <> ", %" <> predecessor <> " ]"
        | (result, predecessor) <- incoming])
  _ -> failCodegen source "llvm-polymorphic-variant"
    "Basis.match is missing its resolved variant row and result type"

lowerSubform
  :: ModuleContext -> M.Expr -> String -> [M.StaticArg] -> Deferred -> Codegen Operand
lowerSubform context source marker staticArguments xml = case reverse staticArguments of
  M.StaticName name : _ -> do
    xml' <- force context xml
    ensureOperand source Ptr xml'
    let prefix = "<input type=\"hidden\" name=\"" <> marker <> "\" value=\""
    withName <- lowerStringConcatOperands source
      (stringOperand context (ByteString8.pack prefix))
      (stringOperand context (ByteString8.pack name))
    opened <- lowerStringConcatOperands source withName
      (stringOperand context (ByteString8.pack "\" />"))
    withXml <- lowerStringConcatOperands source opened xml'
    lowerStringConcatOperands source withXml
      (stringOperand context (ByteString8.pack "<input type=\"hidden\" name=\".e\" value=\"1\" />"))
  _ -> failCodegen source "llvm-subform" "Subform markup is missing its resolved field name"

lowerSubformEntry :: ModuleContext -> M.Expr -> Deferred -> Codegen Operand
lowerSubformEntry context source xml = do
  xml' <- force context xml
  ensureOperand source Ptr xml'
  opened <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "<input type=\"hidden\" name=\".i\" value=\"1\" />")) xml'
  lowerStringConcatOperands source opened
    (stringOperand context (ByteString8.pack "<input type=\"hidden\" name=\".e\" value=\"1\" />"))

lowerSqlIf
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Deferred -> Codegen Operand
lowerSqlIf context source condition yes no = do
  condition' <- force context condition
  yes' <- force context yes
  no' <- force context no
  mapM_ (ensureOperand source Ptr) [condition', yes', no']
  opened <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "(CASE WHEN ")) condition'
  withThen <- lowerStringConcatOperands source opened
    (stringOperand context (ByteString8.pack " THEN "))
  withYes <- lowerStringConcatOperands source withThen yes'
  withElse <- lowerStringConcatOperands source withYes
    (stringOperand context (ByteString8.pack " ELSE "))
  withNo <- lowerStringConcatOperands source withElse no'
  lowerStringConcatOperands source withNo
    (stringOperand context (ByteString8.pack " END)"))

lowerSqlUnary :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerSqlUnary context source operator value = do
  operator' <- force context operator
  value' <- force context value
  mapM_ (ensureOperand source Ptr) [operator', value']
  opened <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "(")) operator'
  spaced <- lowerStringConcatOperands source opened
    (stringOperand context (ByteString8.pack " "))
  withValue <- lowerStringConcatOperands source spaced value'
  lowerStringConcatOperands source withValue
    (stringOperand context (ByteString8.pack ")"))

lowerSqlBinary
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Deferred -> Codegen Operand
lowerSqlBinary context source operator left right = do
  operator' <- force context operator
  left' <- force context left
  right' <- force context right
  mapM_ (ensureOperand source Ptr) [operator', left', right']
  emitResult Ptr
    ("call ptr @vr_runtime_sql_binary(" <> typed operator' <> ", "
      <> typed left' <> ", " <> typed right' <> ")")

lowerSqlDelete :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerSqlDelete context source table predicate = do
  table' <- force context table
  predicate' <- force context predicate
  mapM_ (ensureOperand source Ptr) [table', predicate']
  predicateWithoutAlias <- emitResult Ptr
    ("call ptr @vr_runtime_database_unalias(" <> typed predicate' <> ")")
  opened <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "DELETE FROM ")) table'
  withWhere <- lowerStringConcatOperands source opened
    (stringOperand context (ByteString8.pack " WHERE "))
  lowerStringConcatOperands source withWhere predicateWithoutAlias

lowerSqlUpdate
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Deferred -> Codegen Operand
lowerSqlUpdate context source fields table predicate = do
  fields' <- force context fields
  table' <- force context table
  predicate' <- force context predicate
  mapM_ (ensureOperand source Ptr) [table', predicate']
  assignments <- case operandType fields' of
    I8 -> pure []
    recordType@(Record described) -> forM (zip [0 :: Int ..] described) $ \(index, (name, typ)) -> do
      value <- emitResult typ
        ("extractvalue " <> renderType recordType <> " " <> operandText fields' <> ", " <> show index)
      ensureOperand source Ptr value
      valueWithoutAlias <- emitResult Ptr
        ("call ptr @vr_runtime_database_unalias(" <> typed value <> ")")
      named <- lowerStringConcatOperands source
        (stringOperand context (ByteString8.pack (sqlColumnIdentifier context name)))
        (stringOperand context (ByteString8.pack " = "))
      lowerStringConcatOperands source named valueWithoutAlias
    actual -> failCodegen source "llvm-update"
      ("SQL update fields received " <> renderType actual)
  case assignments of
    [] -> pure (stringOperand context ByteString.empty)
    _ -> do
      assignmentSql <- joinSqlPieces context source assignments
      opened <- lowerStringConcatOperands source
        (stringOperand context (ByteString8.pack "UPDATE ")) table'
      withSet <- lowerStringConcatOperands source opened
        (stringOperand context (ByteString8.pack " SET "))
      withAssignments <- lowerStringConcatOperands source withSet assignmentSql
      withWhere <- lowerStringConcatOperands source withAssignments
        (stringOperand context (ByteString8.pack " WHERE "))
      predicateWithoutAlias <- emitResult Ptr
        ("call ptr @vr_runtime_database_unalias(" <> typed predicate' <> ")")
      lowerStringConcatOperands source withWhere predicateWithoutAlias

lowerNextval :: ModuleContext -> M.Expr -> Deferred -> Codegen Operand
lowerNextval context source sequenceName = do
  name <- force context sequenceName
  ensureOperand source Ptr name
  makeUnitClosure context source "nextval" I64 [name] $ \captures -> case captures of
    [capturedName] -> emitResult I64
      ("call i64 @vr_runtime_database_nextval(" <> typed capturedName <> ")")
    _ -> failCodegen source "llvm-sequence" "Internal nextval capture mismatch"

lowerSetval :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerSetval context source sequenceName value = do
  name <- force context sequenceName
  value' <- force context value
  ensureOperand source Ptr name
  ensureOperand source I64 value'
  makeUnitClosure context source "setval" I8 [name, value'] $ \captures -> case captures of
    [capturedName, capturedValue] -> do
      emitInstruction
        ("call void @vr_runtime_database_setval(" <> typed capturedName <> ", " <> typed capturedValue <> ")")
      pure (Operand I8 "0")
    _ -> failCodegen source "llvm-sequence" "Internal setval capture mismatch"

lowerSqlFrom
  :: ModuleContext -> M.Expr -> [M.StaticArg] -> Bool -> Deferred -> Codegen Operand
lowerSqlFrom context source staticArguments nested value = do
  value' <- force context value
  ensureOperand source Ptr value'
  alias <- case [name | M.StaticName name <- staticArguments] of
    [] -> failCodegen source "llvm-sql-from" "SQL source has no resolved table alias"
    names -> pure (last names)
  aliased <- if nested
    then do
      opened <- lowerStringConcatOperands source
        (stringOperand context (ByteString8.pack "(")) value'
      closed <- lowerStringConcatOperands source opened
        (stringOperand context (ByteString8.pack ")"))
      lowerStringConcatOperands source closed
        (stringOperand context (ByteString8.pack " AS T_"))
    else lowerStringConcatOperands source value'
      (stringOperand context (ByteString8.pack " AS T_"))
  lowerStringConcatOperands source aliased
    (stringOperand context (ByteString8.pack alias))

lowerSqlComma :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerSqlComma context source left right = do
  left' <- force context left
  right' <- force context right
  ensureOperand source Ptr left'
  ensureOperand source Ptr right'
  emitResult Ptr
    ("call ptr @vr_runtime_sql_comma(" <> typed left' <> ", " <> typed right' <> ")")

lowerSqlJoin
  :: ModuleContext -> M.Expr -> String -> Deferred -> Deferred -> Deferred -> Codegen Operand
lowerSqlJoin context source joiner left right predicate = do
  left' <- force context left
  right' <- force context right
  predicate' <- force context predicate
  mapM_ (ensureOperand source Ptr) [left', right', predicate']
  emitResult Ptr
    ("call ptr @vr_runtime_sql_join(" <> typed left' <> ", "
      <> typed (stringOperand context (ByteString8.pack joiner)) <> ", "
      <> typed right' <> ", " <> typed predicate' <> ")")

lowerSqlAggregate
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Codegen Operand
lowerSqlAggregate context source operator expression = do
  operator' <- force context operator
  expression' <- force context expression
  mapM_ (ensureOperand source Ptr) [operator', expression']
  opened <- lowerStringConcatOperands source operator'
    (stringOperand context (ByteString8.pack "("))
  withExpression <- lowerStringConcatOperands source opened expression'
  lowerStringConcatOperands source withExpression
    (stringOperand context (ByteString8.pack ")"))

lowerSqlNumberClause :: ModuleContext -> M.Expr -> String -> Deferred -> Codegen Operand
lowerSqlNumberClause context source prefix value = do
  value' <- force context value
  ensureOperand source I64 value'
  shown <- emitResult Ptr ("call ptr @vr_runtime_urlify_int(" <> typed value' <> ")")
  lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack prefix)) shown

lowerSqlOrder
  :: ModuleContext -> M.Expr -> Deferred -> Deferred -> Deferred -> Codegen Operand
lowerSqlOrder context source expression direction rest = do
  expression' <- force context expression
  direction' <- force context direction
  rest' <- force context rest
  mapM_ (ensureOperand source Ptr) [expression', direction', rest']
  first <- lowerStringConcatOperands source expression' direction'
  emitResult Ptr
    ("call ptr @vr_runtime_sql_comma(" <> typed first <> ", " <> typed rest' <> ")")

lowerSqlQuery :: ModuleContext -> M.Expr -> Deferred -> Codegen Operand
lowerSqlQuery context source record = do
  record' <- force context record
  rows <- extractRecordOperandField source record' "Rows"
  orderBy <- extractRecordOperandField source record' "OrderBy"
  limit <- extractRecordOperandField source record' "Limit"
  offset <- extractRecordOperandField source record' "Offset"
  mapM_ (ensureOperand source Ptr) [rows, orderBy, limit, offset]
  orderClause <- emitResult Ptr
    ("call ptr @vr_runtime_sql_clause("
      <> typed (stringOperand context (ByteString8.pack " ORDER BY ")) <> ", "
      <> typed orderBy <> ", i1 0)")
  foldM (lowerStringConcatOperands source) rows [orderClause, limit, offset]

lowerSqlQuery1
  :: ModuleContext -> M.Expr -> [M.StaticArg] -> Deferred -> Codegen Operand
lowerSqlQuery1 context source staticArguments record = do
  record' <- force context record
  distinct <- extractRecordOperandField source record' "Distinct"
  from <- extractRecordOperandField source record' "From"
  where' <- extractRecordOperandField source record' "Where"
  having <- extractRecordOperandField source record' "Having"
  selectExps <- extractRecordOperandField source record' "SelectExps"
  ensureOperand source I1 distinct
  mapM_ (ensureOperand source Ptr) [from, where', having]

  let selectedFields = case drop 4 staticArguments of
        fields : _ -> staticNestedRow fields
        [] -> []
      tables = case drop 2 staticArguments of
        fields : _ -> staticNestedRow fields
        [] -> []
      grouped = case drop 3 staticArguments of
        fields : _ -> staticNestedRow fields
        [] -> []
      selectedExpressions = case drop 5 staticArguments of
        fields : _ -> map fst (staticFlatRow fields)
        [] -> []
  expressionColumns <- case operandType selectExps of
    I8 -> pure []
    Record described -> forM expressionOrder $ \name -> do
      (index, typ) <- case lookupField name described of
        Just found -> pure found
        Nothing -> failCodegen source "llvm-sql-query"
          ("SQL selected-expression record has no field " <> name)
      expression <- emitResult typ
        ("extractvalue " <> renderType (operandType selectExps) <> " "
          <> operandText selectExps <> ", " <> show index)
      ensureOperand source Ptr expression
      withAlias <- lowerStringConcatOperands source expression
        (stringOperand context (ByteString8.pack aliasOpen))
      withName <- lowerStringConcatOperands source withAlias
        (stringOperand context (ByteString8.pack name))
      lowerStringConcatOperands source withName
        (stringOperand context (ByteString8.pack aliasClose))
      where
        (aliasOpen, aliasClose) = case moduleDatabaseSystem context of
          DatabaseMySQL -> (" AS `", "`")
          _ -> (" AS \"", "\"")
        expressionOrder
          | null selectedExpressions = map fst described
          | otherwise = selectedExpressions
    actual -> failCodegen source "llvm-sql-query"
      ("SQL selected expressions received " <> renderType actual)
  tableColumns <- mapM (renderSelectedColumn context source) selectedFields
  selection <- case expressionColumns <> concat tableColumns of
    [] -> pure (stringOperand context (ByteString8.pack "0"))
    columns -> joinSqlPieces context source columns
  distinctText <- chooseSqlText context source distinct "DISTINCT " ""
  queryStart <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "SELECT ")) distinctText
  withSelection <- lowerStringConcatOperands source queryStart selection
  fromClause <- sqlClause context source " FROM " False from
  whereClause <- sqlClause context source " WHERE " True where'
  groupClause <- if sqlGroupingRequired tables grouped
    then do
      groupedColumns <- fmap concat (mapM (renderGroupedColumn context source) grouped)
      groupSql <- joinSqlPieces context source groupedColumns
      lowerStringConcatOperands source
        (stringOperand context (ByteString8.pack " GROUP BY ")) groupSql
    else pure (stringOperand context ByteString.empty)
  havingClause <- sqlClause context source " HAVING " True having
  foldM (lowerStringConcatOperands source) withSelection
    [fromClause, whereClause, groupClause, havingClause]

renderSelectedColumn
  :: ModuleContext -> M.Expr -> (String, [(String, M.StaticArg)]) -> Codegen [Operand]
renderSelectedColumn context source (table, fields) = forM fields $ \(field, _) -> do
  qualified <- renderQualifiedColumn context source table field
  withAlias <- lowerStringConcatOperands source qualified
    (stringOperand context (ByteString8.pack aliasOpen))
  withPrefix <- lowerStringConcatOperands source withAlias
    (stringOperand context (ByteString8.pack "vr__"))
  withTable <- lowerStringConcatOperands source withPrefix
    (stringOperand context (ByteString8.pack table))
  withSeparator <- lowerStringConcatOperands source withTable
    (stringOperand context (ByteString8.pack "__"))
  withField <- lowerStringConcatOperands source withSeparator
    (stringOperand context (ByteString8.pack field))
  lowerStringConcatOperands source withField
    (stringOperand context (ByteString8.pack aliasClose))
  where
    (aliasOpen, aliasClose) = case moduleDatabaseSystem context of
      DatabaseMySQL -> (" AS `", "`")
      _ -> (" AS \"", "\"")

renderGroupedColumn
  :: ModuleContext -> M.Expr -> (String, [(String, M.StaticArg)]) -> Codegen [Operand]
renderGroupedColumn context source (table, fields) =
  mapM (renderQualifiedColumn context source table . fst) fields

renderQualifiedColumn :: ModuleContext -> M.Expr -> String -> String -> Codegen Operand
renderQualifiedColumn context source table field = do
  withTable <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "T_"))
    (stringOperand context (ByteString8.pack table))
  withDot <- lowerStringConcatOperands source withTable
    (stringOperand context (ByteString8.pack "."))
  lowerStringConcatOperands source withDot
    (stringOperand context (ByteString8.pack (sqlColumnIdentifier context field)))

staticNestedRow :: M.StaticArg -> [(String, [(String, M.StaticArg)])]
staticNestedRow (M.StaticRow tables) =
  [ (table, [(field, typ) | (M.StaticName field, typ) <- fields])
  | (M.StaticName table, M.StaticRow fields) <- tables
  ]
staticNestedRow _ = []

staticFlatRow :: M.StaticArg -> [(String, M.StaticArg)]
staticFlatRow (M.StaticRow fields) =
  [(name, typ) | (M.StaticName name, typ) <- fields]
staticFlatRow _ = []

sqlGroupingRequired
  :: [(String, [(String, M.StaticArg)])]
  -> [(String, [(String, M.StaticArg)])]
  -> Bool
sqlGroupingRequired tables grouped = any missing tables
  where
    missing (table, fields) = case lookup table grouped of
      Nothing -> not (null fields)
      Just groupedFields -> any (\(field, _) -> field `notElem` map fst groupedFields) fields

sqlClause :: ModuleContext -> M.Expr -> String -> Bool -> Operand -> Codegen Operand
sqlClause context source prefix skipTrue value = do
  ensureOperand source Ptr value
  emitResult Ptr
    ("call ptr @vr_runtime_sql_clause("
      <> typed (stringOperand context (ByteString8.pack prefix)) <> ", "
      <> typed value <> ", i1 " <> llvmBool skipTrue <> ")")

chooseSqlText :: ModuleContext -> M.Expr -> Operand -> String -> String -> Codegen Operand
chooseSqlText context source condition yes no = do
  ensureOperand source I1 condition
  yesLabel <- freshLabel "sql_text_yes"
  noLabel <- freshLabel "sql_text_no"
  mergeLabel <- freshLabel "sql_text_merge"
  emitInstruction ("br i1 " <> operandText condition <> ", label %" <> yesLabel <> ", label %" <> noLabel)
  emitBlock yesLabel
  let yesValue = stringOperand context (ByteString8.pack yes)
  yesBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock noLabel
  let noValue = stringOperand context (ByteString8.pack no)
  noBlock <- gets codegenCurrentBlock
  emitInstruction ("br label %" <> mergeLabel)
  emitBlock mergeLabel
  emitResult Ptr
    ("phi ptr [ " <> operandText yesValue <> ", %" <> yesBlock <> " ], [ "
      <> operandText noValue <> ", %" <> noBlock <> " ]")

extractRecordOperandField :: M.Expr -> Operand -> String -> Codegen Operand
extractRecordOperandField source aggregate name = case operandType aggregate of
  Record fields -> case lookupField name fields of
    Just (index, typ) -> emitResult typ
      ("extractvalue " <> renderType (operandType aggregate) <> " "
        <> operandText aggregate <> ", " <> show index)
    Nothing -> failCodegen source "llvm-record-field"
      ("Record has no field " <> name)
  actual -> failCodegen source "llvm-record-field"
    ("Field selection received " <> renderType actual)

lowerSqlFold
  :: ModuleContext
  -> M.Expr
  -> [M.StaticArg]
  -> Deferred
  -> Deferred
  -> Deferred
  -> Codegen Operand
lowerSqlFold context source staticArguments query callback initial = case staticArguments of
  tableShape : expressionShape : stateShape : _ -> do
    query' <- force context query
    callback' <- force context callback
    stateType <- liftEither (lowerStaticTypeAt (locatedSpan source) stateShape)
    initial' <- forceExpected context stateType initial
    ensureOperand source Ptr query'
    makeUnitClosure context source "query" stateType [query', callback', initial'] $ \captures -> case captures of
      [capturedQuery, capturedCallback, capturedInitial] -> do
        statement <- emitResult Ptr
          ("call ptr @vr_runtime_database_prepare(" <> typed capturedQuery <> ")")
        stateAddress <- allocate stateType
        emitInstruction ("store " <> typed capturedInitial <> ", ptr " <> operandText stateAddress)
        loopLabel <- freshLabel "query_loop"
        rowLabel <- freshLabel "query_row"
        continueLabel <- freshLabel "query_continue"
        doneLabel <- freshLabel "query_done"
        emitInstruction ("br label %" <> loopLabel)
        emitBlock loopLabel
        emitInstruction "call void @vr_runtime_check_deadline()"
        hasRow <- emitResult I1 ("call i1 @vr_runtime_database_step(" <> typed statement <> ")")
        emitInstruction ("br i1 " <> operandText hasRow <> ", label %" <> rowLabel <> ", label %" <> doneLabel)
        emitBlock rowLabel
        rowType <- case operandType capturedCallback of
          Function domain _ -> pure domain
          actual -> failCodegen source "llvm-query"
            ("SQL callback received " <> renderType actual)
        row <- lowerDatabaseRow context source statement tableShape expressionShape rowType
        state <- emitResult stateType
          ("load " <> renderType stateType <> ", ptr " <> operandText stateAddress)
        withRow <- applyClosure context source capturedCallback (Lowered row)
        withState <- applyClosure context source withRow (Lowered state)
        next <- runTransactionOperand context source withState
        ensureOperand source stateType next
        emitInstruction ("store " <> typed next <> ", ptr " <> operandText stateAddress)
        emitInstruction ("br label %" <> continueLabel)
        emitBlock continueLabel
        emitInstruction ("br label %" <> loopLabel)
        emitBlock doneLabel
        emitInstruction ("call void @vr_runtime_database_finalize(" <> typed statement <> ")")
        emitResult stateType
          ("load " <> renderType stateType <> ", ptr " <> operandText stateAddress)
      _ -> failCodegen source "llvm-query" "Internal SQL query capture mismatch"
  _ -> failCodegen source "llvm-query" "Basis.query has incomplete static row and state arguments"

lowerDatabaseRow
  :: ModuleContext -> M.Expr -> Operand -> M.StaticArg -> M.StaticArg -> LlvmType -> Codegen Operand
lowerDatabaseRow context source statement tableShape expressionShape expectedType = do
  let expressions = staticFlatRow expressionShape
      tables = staticNestedRow tableShape
  (expressionValues, nextColumn) <- lowerDatabaseFields context source statement 0 expressions
  (tableValues, _) <- foldM lowerTable ([], nextColumn) tables
  buildRecordOperandAs source expectedType (expressionValues <> tableValues)
  where
    lowerTable (done, column) (table, fields) = do
      (values, next) <- lowerDatabaseFields context source statement column fields
      nestedType <- case expectedType of
        Record expectedFields -> case lookup table expectedFields of
          Just found -> pure found
          Nothing -> failCodegen source "llvm-query-row"
            ("SQL callback row has no table " <> table)
        actual -> failCodegen source "llvm-query-row"
          ("SQL callback row received " <> renderType actual)
      nested <- buildRecordOperandAs source nestedType values
      pure (done <> [(table, nested)], next)

lowerDatabaseFields
  :: ModuleContext
  -> M.Expr
  -> Operand
  -> Int
  -> [(String, M.StaticArg)]
  -> Codegen ([(String, Operand)], Int)
lowerDatabaseFields context source statement first fields = do
  values <- forM (zip [first ..] fields) $ \(column, (name, typ)) -> do
    value <- lowerDatabaseColumn context source statement column typ
    pure (name, value)
  pure (values, first + length fields)

lowerDatabaseColumn
  :: ModuleContext -> M.Expr -> Operand -> Int -> M.StaticArg -> Codegen Operand
lowerDatabaseColumn context source statement column typ = case typ of
  M.StaticFfi "Basis" "option" [element] -> do
    missing <- emitResult I1
      ("call i1 @vr_runtime_database_column_is_null(" <> typed statement <> ", i64 " <> show column <> ")")
    noneLabel <- freshLabel "db_none"
    someLabel <- freshLabel "db_some"
    mergeLabel <- freshLabel "db_option_merge"
    emitInstruction ("br i1 " <> operandText missing <> ", label %" <> noneLabel <> ", label %" <> someLabel)
    emitBlock noneLabel
    none <- allocateTagged context source 0 Nothing
    noneBlock <- gets codegenCurrentBlock
    emitInstruction ("br label %" <> mergeLabel)
    emitBlock someLabel
    payload <- lowerDatabaseColumn context source statement column element
    some <- allocateTagged context source 1 (Just payload)
    someBlock <- gets codegenCurrentBlock
    emitInstruction ("br label %" <> mergeLabel)
    emitBlock mergeLabel
    emitResult Ptr
      ("phi ptr [ " <> operandText none <> ", %" <> noneBlock <> " ], [ "
        <> operandText some <> ", %" <> someBlock <> " ]")
  M.StaticFfi "Basis" "int" _ -> integer
  M.StaticFfi "Basis" "bool" _ -> do
    value <- integer
    emitResult I1 ("icmp ne i64 " <> operandText value <> ", 0")
  M.StaticFfi "Basis" "float" _ ->
    emitResult F64 ("call double @vr_runtime_database_column_float(" <> args <> ")")
  M.StaticFfi "Basis" "char" _ -> do
    value <- textColumn
    emitResult I32 ("call i32 @vr_runtime_form_char(" <> typed value <> ")")
  M.StaticFfi "Basis" "time" _ ->
    emitResult Ptr ("call ptr @vr_runtime_database_column_time(" <> args <> ")")
  M.StaticFfi "Basis" "blob" _ ->
    emitResult Ptr ("call ptr @vr_runtime_database_column_blob(" <> args <> ")")
  M.StaticFfi "Basis" "channel" _ -> do
    combined <- integer
    emitResult Ptr ("call ptr @vr_runtime_channel_from_sql(" <> typed combined <> ")")
  M.StaticFfi "Basis" "client" _ -> do
    number <- integer
    number32 <- emitResult I32 ("trunc i64 " <> operandText number <> " to i32")
    emitResult Ptr ("call ptr @vr_runtime_client_from_number(" <> typed number32 <> ")")
  M.StaticFfi "Basis" _ _ -> textColumn
  M.StaticType monoType -> do
    staticType <- liftEither (lowerTypeAt (locatedSpan source) monoType)
    case staticType of
      I64 -> integer
      F64 -> emitResult F64 ("call double @vr_runtime_database_column_float(" <> args <> ")")
      Ptr -> textColumn
      other -> failCodegen source "llvm-query-column"
        ("Unsupported SQL result type " <> renderType other)
  _ -> failCodegen source "llvm-query-column" "Unsupported static SQL result type"
  where
    args = typed statement <> ", i64 " <> show column
    integer = emitResult I64 ("call i64 @vr_runtime_database_column_int(" <> args <> ")")
    textColumn = emitResult Ptr ("call ptr @vr_runtime_database_column_text(" <> args <> ")")

buildRecordOperand :: Located value -> [(String, Operand)] -> Codegen Operand
buildRecordOperand source fields = do
  let typ = Record [(name, operandType value) | (name, value) <- fields]
  foldM insert (Operand typ "undef") (zip [0 :: Int ..] fields)
  where
    insert aggregate (index, (_, value)) = do
      let typ = operandType aggregate
      ensureOperand source (case typ of Record described -> snd (described !! index); _ -> operandType value) value
      emitResult typ
        ("insertvalue " <> renderType typ <> " " <> operandText aggregate <> ", "
          <> typed value <> ", " <> show index)

buildRecordOperandAs :: Located value -> LlvmType -> [(String, Operand)] -> Codegen Operand
buildRecordOperandAs source expected fields = case expected of
  Record described -> do
    ordered <- forM described $ \(name, typ) -> case lookup name fields of
      Just value -> ensureOperand source typ value >> pure (name, value)
      Nothing -> failCodegen source "llvm-query-row"
        ("SQL row has no selected field " <> name)
    buildRecordOperand source ordered
  I8 | null fields -> pure (Operand I8 "0")
  actual -> failCodegen source "llvm-query-row"
    ("SQL row cannot populate " <> renderType actual)

lowerHtmlTag :: ModuleContext -> M.Expr -> [Deferred] -> Codegen Operand
lowerHtmlTag context source arguments
  | Just (name, code) <- clientCodeTag arguments
  , Just identifier <- Map.lookup code (moduleClientActives context) =
      lowerClientIsland context source name code identifier
  | Just signal <- dynamicSignalTag arguments
  , Just identifier <- Map.lookup signal (moduleClientDynamics context) =
      lowerClientDynamic context source signal identifier
  | Just clientSource <- dynamicSourceTag arguments = do
      identifier <- lowerExpr context clientSource
      ensureOperand source Ptr identifier
      opening <- lowerStringConcatOperands source
        (stringOperand context (ByteString8.pack "<span data-vr-dyn-source=\"")) identifier
      lowerStringConcatOperands source opening
        (stringOperand context (ByteString8.pack "\"></span>"))
  | otherwise = lowerOrdinaryHtmlTag context source True arguments

lowerOrdinaryHtmlTag :: ModuleContext -> M.Expr -> Bool -> [Deferred] -> Codegen Operand
lowerOrdinaryHtmlTag context source includeClosing arguments = case arguments of
  [dataAttributes, dynamicAttributes, style, dynamicStyle, attributes, descriptor, child] -> do
    auxiliaries <- mapM (deferredExpression source) [dataAttributes, dynamicAttributes, style, dynamicStyle]
    renderedAuxiliaries <- lowerHtmlAuxiliaries context source auxiliaries
    descriptorExpression <- deferredExpression source descriptor
    rawName <- case htmlBasisTagName descriptorExpression of
      Just found -> pure found
      Nothing -> failCodegen source "llvm-html-tag" "HTML tag descriptor is not statically known"
    let name = htmlElementName rawName
    attributesExpression <- deferredExpression source attributes
    let buttonValues = case locatedValue attributesExpression of
          M.ERecord fields | name == "button" ->
            [value | (M.StaticName "Value", value, _) <- fields]
          _ -> []
        renderedAttributesExpression = case (buttonValues, locatedValue attributesExpression) of
          ([_], M.ERecord fields) -> Located (locatedSpan attributesExpression)
            (M.ERecord
              [field | field@(fieldName, _, _) <- fields, fieldName /= M.StaticName "Value"])
          _ -> attributesExpression
    ordinaryAttributes <- lowerHtmlAttributes context source (clientControlKind rawName)
      renderedAttributesExpression
    renderedAttributes <- lowerStringConcatOperands source renderedAuxiliaries ordinaryAttributes
    renderedAttributes' <- case htmlContainerControlName name descriptorExpression of
      Nothing -> pure renderedAttributes
      Just fieldName -> do
        withPrefix <- lowerStringConcatOperands source renderedAttributes
          (stringOperand context (ByteString8.pack " name=\""))
        withName <- lowerStringConcatOperands source withPrefix
          (stringOperand context (ByteString8.pack fieldName))
        lowerStringConcatOperands source withName (stringOperand context (ByteString8.pack "\""))
    child' <- force context child
    ensureOperand source Ptr child'
    renderedChild <- case buttonValues of
      [buttonValue] -> do
        buttonValue' <- lowerExpr context buttonValue
        ensureOperand source Ptr buttonValue'
        lowerStringConcatOperands source buttonValue' child'
      _ -> pure child'
    case htmlControlInfo descriptorExpression of
      Just (inputType, fieldName) -> emitResult Ptr
        ("call ptr @vr_runtime_render_input("
          <> typed (stringOperand context (ByteString8.pack inputType)) <> ", "
          <> typed (stringOperand context (ByteString8.pack (maybe "" id fieldName))) <> ", "
          <> typed renderedAttributes' <> ")")
      Nothing -> do
        let (openingText, openingEndText, closingText) = htmlTagFragments name
            literal text = primitiveOperand context (locatedSpan source)
              (PrimString HtmlString (ByteString8.pack text))
        -- Synthesized tag fragments obey the same checked string-table
        -- invariant as source literals. A missing entry is a compiler
        -- diagnostic, never a null pointer passed to strlen at runtime.
        openingStart <- literal openingText
        openingEnd <- literal openingEndText
        closing <- literal closingText
        opening <- if staticEmptyString renderedAttributes'
          then literal (openingText <> openingEndText)
          else do
            startWithAttributes <- lowerStringConcatOperands source openingStart renderedAttributes'
            lowerStringConcatOperands source startWithAttributes openingEnd
        withOpening <- lowerStringConcatOperands source opening renderedChild
        if includeClosing
          then lowerStringConcatOperands source withOpening closing
          else pure withOpening
  _ -> failCodegen source "llvm-html-tag" "Basis.tag has too few runtime arguments"

clientCodeTag :: [Deferred] -> Maybe (String, M.Expr)
clientCodeTag arguments = case arguments of
  [_, _, _, _, DeferredExpr attributes, DeferredExpr descriptor, _]
    | Just name <- htmlTagName descriptor
    , name `elem` ["active", "script"]
    , M.ERecord fields <- locatedValue attributes -> case
        [ value
        | (M.StaticName "Code", value, _) <- fields
        ] of
          [value] -> Just (name, value)
          _ -> Nothing
  _ -> Nothing

dynamicSignalTag :: [Deferred] -> Maybe M.Expr
dynamicSignalTag arguments = case arguments of
  [_, _, _, _, DeferredExpr attributes, DeferredExpr descriptor, _]
    | htmlTagName descriptor == Just "dyn"
    , M.ERecord fields <- locatedValue attributes -> case
        [ value
        | (M.StaticName "Signal", value, _) <- fields
        ] of
          [value] -> Just value
          _ -> Nothing
  _ -> Nothing

dynamicSourceTag :: [Deferred] -> Maybe M.Expr
dynamicSourceTag arguments = dynamicSignalTag arguments >>= directSignalSource

directSignalSource :: M.Expr -> Maybe M.Expr
directSignalSource expression = case locatedValue expression of
  M.ESignalSource value -> Just value
  M.EApp function argument -> case locatedValue function of
    M.EAbs _ _ _ body -> case locatedValue body of
      M.ESignalSource local
        | M.ERel 0 <- locatedValue local -> Just argument
      _ -> Nothing
    _ -> Nothing
  _ -> Nothing

lowerHtmlAuxiliaries :: ModuleContext -> M.Expr -> [M.Expr] -> Codegen Operand
lowerHtmlAuxiliaries context source expressions = case expressions of
  [classes, dynamicClasses, style, dynamicStyle] -> do
    renderedClasses <- renderOptional "null" "class" classes
    renderedDynamicClasses <- renderDynamic "class" dynamicClasses
    renderedStyle <- renderOptional "noStyle" "style" style
    renderedDynamicStyle <- renderDynamic "style" dynamicStyle
    classAttributes <- lowerStringConcatOperands source renderedClasses renderedDynamicClasses
    styleAttributes <- lowerStringConcatOperands source renderedStyle renderedDynamicStyle
    lowerStringConcatOperands source classAttributes styleAttributes
  _ -> failCodegen source "llvm-html-client-attribute" "Malformed HTML class/style arguments"
  where
    renderOptional emptyName attributeName expression = case locatedValue expression of
      M.EFfi "Basis" actual _ | actual == emptyName -> pure (stringOperand context ByteString.empty)
      M.EPrim (PrimString _ bytes) | ByteString.null bytes ->
        pure (stringOperand context ByteString.empty)
      _ -> do
        raw <- lowerExpr context expression
        ensureOperand source Ptr raw
        escaped <- emitResult Ptr ("call ptr @vr_runtime_attrify_string(" <> typed raw <> ")")
        withPrefix <- lowerStringConcatOperands source
          (stringOperand context (ByteString8.pack (" " <> attributeName <> "=\""))) escaped
        lowerStringConcatOperands source withPrefix (stringOperand context (ByteString8.pack "\""))
    renderDynamic kind option = case locatedValue option of
      M.ENone {} -> pure (stringOperand context ByteString.empty)
      M.ESome _ signal -> case Map.lookup signal (moduleClientDynamics context) of
        Just identifier -> lowerClientAttributeSignal context source kind signal identifier
        Nothing -> failCodegen source "llvm-html-client-attribute"
          "Dynamic class/style signal was not registered for browser lowering"
      _ -> failCodegen source "llvm-html-client-attribute"
        "Absence or presence of a dynamic class/style signal is not statically known"

lowerHtmlAttributes :: ModuleContext -> M.Expr -> Maybe String -> M.Expr -> Codegen Operand
lowerHtmlAttributes context source controlKind expression = case locatedValue expression of
  M.ERecord fields -> foldM renderOne (stringOperand context ByteString.empty) fields
  _ -> failCodegen source "llvm-html-attributes" "HTML attributes are not represented by a concrete record"
  where
    renderOne rendered (name, value, _) = case name of
      M.StaticName fieldName -> case Map.lookup value (moduleClientHandlers context) of
        Just identifier -> do
          let captures = Map.findWithDefault [] value (moduleClientCaptures context)
          renderedHandler <- if null captures
            then pure (stringOperand context (ByteString8.pack (clientHandlerAttribute fieldName identifier)))
            else lowerCapturedClientHandler context value fieldName identifier captures
          lowerStringConcatOperands source rendered renderedHandler
        Nothing
          | take 2 fieldName == "On" -> failCodegen value "llvm-html-client-capture"
              "This browser event handler captures a server value; client hydration is not implemented yet"
          | fieldName == "Data" -> do
              raw <- lowerRecordValue context source fieldName value
              ensureOperand source Ptr raw
              withSpace <- lowerStringConcatOperands source rendered
                (stringOperand context (ByteString8.pack " "))
              lowerStringConcatOperands source withSpace raw
          | fieldName == "Source", Just kind <- controlKind -> do
              identifier <- lowerExpr context value
              ensureOperand source Ptr identifier
              escaped <- emitResult Ptr ("call ptr @vr_runtime_attrify_string(" <> typed identifier <> ")")
              withSourcePrefix <- lowerStringConcatOperands source rendered
                (stringOperand context (ByteString8.pack " data-vr-control-source=\""))
              withSource <- lowerStringConcatOperands source withSourcePrefix escaped
              withSourceSuffix <- lowerStringConcatOperands source withSource
                (stringOperand context (ByteString8.pack "\" data-vr-control-kind=\""))
              withKind <- lowerStringConcatOperands source withSourceSuffix
                (stringOperand context (ByteString8.pack kind))
              lowerStringConcatOperands source withKind (stringOperand context (ByteString8.pack "\""))
          | otherwise -> do
              raw <- lowerRecordValue context source fieldName value
              let normalizedName = htmlAttributeName fieldName
              case operandType raw of
                I1 -> do
                  selected <- emitResult Ptr
                    ("select i1 " <> operandText raw <> ", "
                      <> typed (stringOperand context (ByteString8.pack (" " <> normalizedName))) <> ", "
                      <> typed (stringOperand context ByteString.empty))
                  lowerStringConcatOperands source rendered selected
                _ -> do
                  textValue <- htmlAttributeText source raw
                  escaped <- emitResult Ptr ("call ptr @vr_runtime_attrify_string(" <> typed textValue <> ")")
                  let prefix = stringOperand context (ByteString8.pack (" " <> normalizedName <> "=\""))
                      suffix = stringOperand context (ByteString8.pack "\"")
                  withPrefix <- lowerStringConcatOperands source rendered prefix
                  withValue <- lowerStringConcatOperands source withPrefix escaped
                  lowerStringConcatOperands source withValue suffix
      _ -> failCodegen source "llvm-html-attribute-name" "HTML attribute name is not statically known"

htmlAttributeText :: M.Expr -> Operand -> Codegen Operand
htmlAttributeText source value = case operandType value of
  Ptr -> pure value
  I64 -> emitResult Ptr ("call ptr @vr_runtime_urlify_int(" <> typed value <> ")")
  F64 -> emitResult Ptr ("call ptr @vr_runtime_show_float(" <> typed value <> ")")
  I32 -> emitResult Ptr ("call ptr @vr_runtime_show_char(" <> typed value <> ")")
  actual -> failCodegen source "llvm-html-attribute-type"
    ("HTML attribute has unsupported runtime type " <> renderType actual)

clientHandlerAttribute :: String -> Int -> String
clientHandlerAttribute name identifier =
  clientHandlerAttributeStart name identifier <> "])(event)\""

clientHandlerAttributeStart :: String -> Int -> String
clientHandlerAttributeStart name identifier =
  " " <> htmlAttributeName name
    <> "=\"return globalThis.__vrHandlers[" <> show identifier <> "](["

clientDynamicTagStart :: Int -> String
clientDynamicTagStart identifier =
  "<span data-vr-dyn=\"" <> show identifier
    <> "\" data-vr-captures=\"["

clientDynamicAttributeStart :: String -> Int -> String
clientDynamicAttributeStart kind identifier =
  " data-vr-dyn-" <> kind <> "=\"" <> show identifier
    <> "\" data-vr-dyn-" <> kind <> "-captures=\"["

clientIslandTagStart :: String -> Int -> String
clientIslandTagStart name identifier =
  "<span data-vr-" <> name <> "=\"" <> show identifier
    <> "\" data-vr-captures=\"["

clientClosureStart :: Int -> String
clientClosureStart identifier =
  "globalThis.__vrClosures[" <> show identifier <> "](["

lowerClientIsland
  :: ModuleContext
  -> M.Expr
  -> String
  -> M.Expr
  -> Int
  -> Codegen Operand
lowerClientIsland context source name code identifier = do
  locals <- gets codegenLocals
  let captures = Map.findWithDefault [] code (moduleActiveCaptures context)
      captureTypes = Map.findWithDefault [] code (moduleActiveCaptureTypes context)
  if length captureTypes == length captures
    then pure ()
    else failCodegen source "llvm-html-client-capture"
      "Client block capture metadata is inconsistent"
  captured <- mapM (captureAt locals) (zip captures captureTypes)
  withCaptures <- foldM appendCapture
    (stringOperand context (ByteString8.pack (clientIslandTagStart name identifier)))
    (zip [0 :: Int ..] captured)
  lowerStringConcatOperands source withCaptures
    (stringOperand context (ByteString8.pack "]\"></span>"))
  where
    captureAt locals (index, typ) = case drop index locals of
      value : _ -> do
        serialized <- lowerClientCapture context source typ value
        emitResult Ptr ("call ptr @vr_runtime_attrify_string(" <> typed serialized <> ")")
      [] -> failCodegen source "llvm-html-client-capture"
        ("Client block refers to unavailable local " <> show index)
    appendCapture rendered (captureIndex, value) = do
      separated <- if captureIndex == 0
        then pure rendered
        else lowerStringConcatOperands source rendered
          (stringOperand context (ByteString8.pack ","))
      lowerStringConcatOperands source separated value

lowerClientDynamic :: ModuleContext -> M.Expr -> M.Expr -> Int -> Codegen Operand
lowerClientDynamic context source signal identifier = do
  locals <- gets codegenLocals
  let captures = Map.findWithDefault [] signal (moduleDynamicCaptures context)
      captureTypes = Map.findWithDefault [] signal (moduleDynamicCaptureTypes context)
  if length captureTypes == length captures
    then pure ()
    else failCodegen source "llvm-html-client-capture"
      "Client signal capture metadata is inconsistent"
  captured <- mapM (captureAt locals) (zip captures captureTypes)
  withCaptures <- foldM appendCapture
    (stringOperand context (ByteString8.pack (clientDynamicTagStart identifier)))
    (zip [0 :: Int ..] captured)
  lowerStringConcatOperands source withCaptures
    (stringOperand context (ByteString8.pack "]\"></span>"))
  where
    captureAt locals (index, typ) = case drop index locals of
      value : _ -> do
        serialized <- lowerClientCapture context source typ value
        emitResult Ptr ("call ptr @vr_runtime_attrify_string(" <> typed serialized <> ")")
      [] -> failCodegen source "llvm-html-client-capture"
        ("Client signal refers to unavailable local " <> show index)
    appendCapture rendered (captureIndex, value) = do
      separated <- if captureIndex == 0
        then pure rendered
        else lowerStringConcatOperands source rendered
          (stringOperand context (ByteString8.pack ","))
      lowerStringConcatOperands source separated value

lowerClientAttributeSignal
  :: ModuleContext
  -> M.Expr
  -> String
  -> M.Expr
  -> Int
  -> Codegen Operand
lowerClientAttributeSignal context source kind signal identifier = do
  locals <- gets codegenLocals
  let captures = Map.findWithDefault [] signal (moduleDynamicCaptures context)
      captureTypes = Map.findWithDefault [] signal (moduleDynamicCaptureTypes context)
  if length captureTypes == length captures
    then pure ()
    else failCodegen source "llvm-html-client-capture"
      "Dynamic class/style capture metadata is inconsistent"
  captured <- mapM (captureAt locals) (zip captures captureTypes)
  withCaptures <- foldM appendCapture
    (stringOperand context (ByteString8.pack (clientDynamicAttributeStart kind identifier)))
    (zip [0 :: Int ..] captured)
  lowerStringConcatOperands source withCaptures
    (stringOperand context (ByteString8.pack "]\""))
  where
    captureAt locals (index, typ) = case drop index locals of
      value : _ -> do
        serialized <- lowerClientCapture context source typ value
        emitResult Ptr ("call ptr @vr_runtime_attrify_string(" <> typed serialized <> ")")
      [] -> failCodegen source "llvm-html-client-capture"
        ("Dynamic class/style signal refers to unavailable local " <> show index)
    appendCapture rendered (captureIndex, value) = do
      separated <- if captureIndex == 0
        then pure rendered
        else lowerStringConcatOperands source rendered
          (stringOperand context (ByteString8.pack ","))
      lowerStringConcatOperands source separated value

lowerCapturedClientHandler
  :: ModuleContext
  -> M.Expr
  -> String
  -> Int
  -> [Int]
  -> Codegen Operand
lowerCapturedClientHandler context source name identifier captures = do
  locals <- gets codegenLocals
  let captureTypes = Map.findWithDefault [] source (moduleClientCaptureTypes context)
  if length captureTypes == length captures
    then pure ()
    else failCodegen source "llvm-html-client-capture"
      "Client handler capture metadata is inconsistent"
  captured <- mapM (captureAt locals) (zip captures captureTypes)
  withCaptures <- foldM appendCapture
    (stringOperand context (ByteString8.pack (clientHandlerAttributeStart name identifier)))
    (zip [0 :: Int ..] captured)
  lowerStringConcatOperands source withCaptures
    (stringOperand context (ByteString8.pack "])(event)\""))
  where
    captureAt locals (index, typ) = case drop index locals of
      value : _ -> do
        serialized <- lowerClientCapture context source typ value
        emitResult Ptr ("call ptr @vr_runtime_attrify_string(" <> typed serialized <> ")")
      [] -> failCodegen source "llvm-html-client-capture"
        ("Client handler refers to unavailable local " <> show index)
    appendCapture rendered (captureIndex, value) = do
      separated <- if captureIndex == 0
        then pure rendered
        else lowerStringConcatOperands source rendered
          (stringOperand context (ByteString8.pack ","))
      lowerStringConcatOperands source separated value

lowerClientCapture
  :: ModuleContext
  -> M.Expr
  -> M.Type
  -> Operand
  -> Codegen Operand
lowerClientCapture context source = lowerClientCaptureWith context source Map.empty

lowerClientCaptureWith
  :: ModuleContext
  -> M.Expr
  -> Map.Map M.GlobalId String
  -> M.Type
  -> Operand
  -> Codegen Operand
lowerClientCaptureWith context source recursive typ value = case locatedValue typ of
  M.TSource -> do
    ensureOperand source Ptr value
    opened <- lowerStringConcatOperands source
      (stringOperand context (ByteString8.pack "globalThis.__vrSources[")) value
    lowerStringConcatOperands source opened
      (stringOperand context (ByteString8.pack "]"))
  M.TFfi "Basis" "int" -> encode I64 "vr_runtime_javascript_int"
  M.TFfi "Basis" "float" -> encode F64 "vr_runtime_javascript_float"
  M.TFfi "Basis" "bool" -> encode I1 "vr_runtime_javascript_bool"
  M.TFfi "Basis" "char" -> encode I32 "vr_runtime_javascript_char"
  M.TFfi "Basis" "channel" -> encode Ptr "vr_runtime_javascript_channel"
  M.TFfi "Basis" _ -> encode Ptr "vr_runtime_javascript_string"
  M.TFun {} -> case operandType value of
    Function {} -> do
      literalAddress <- emitResult Ptr
        ("getelementptr inbounds { ptr, ptr, ptr }, ptr " <> operandText value
          <> ", i32 0, i32 2")
      literal <- emitResult Ptr ("load ptr, ptr " <> operandText literalAddress)
      emitResult Ptr ("call ptr @vr_runtime_javascript_closure(" <> typed literal <> ")")
    _ -> failCodegen source "llvm-html-client-capture"
      "Native browser capture received a mismatched function value"
  M.TRecord [] -> do
    ensureOperand source I8 value
    pure (stringOperand context (ByteString8.pack "null"))
  M.TRecord sourceFields -> case operandType value of
    Record fields
      | map fst sourceFields == map fst fields -> do
          encoded <- forM (zip3 [0 :: Int ..] sourceFields fields) $
            \(index, (name, fieldSourceType), (_, fieldType)) -> do
              field <- emitResult fieldType
                ("extractvalue " <> renderType (operandType value) <> " "
                  <> operandText value <> ", " <> show index)
              field' <- lowerClientCaptureWith context source recursive fieldSourceType field
              pure (name, field')
          renderClientRecord context source encoded
    _ -> failCodegen source "llvm-html-client-capture"
      "Native browser capture received a mismatched record value"
  M.TOption element -> do
    ensureOperand source Ptr value
    lowerTaggedUrlEncode context source value
      [ (0, renderClientTagged context source 0 Nothing)
      , (1, do
          elementType <- liftEither (lowerTypeAt (locatedSpan source) element)
          payload <- loadTaggedExprPayload source value elementType
          encoded <- lowerClientCaptureWith context source recursive element payload
          renderClientTagged context source 1 (Just encoded))
      ]
  M.TList element -> do
    ensureOperand source Ptr value
    lowerClientListCapture context source recursive typ element value
  M.TDatatype identifier -> do
    ensureOperand source Ptr value
    case Map.lookup identifier recursive of
      Just helper -> callUrlEncodeHelper helper value
      Nothing -> lowerClientDatatypeCapture context source recursive identifier value
  _ -> failCodegen source "llvm-html-client-capture"
    "Native browser capture serialization does not support this value type yet"
  where
    encode expected function = do
      ensureOperand source expected value
      emitResult Ptr ("call ptr @" <> function <> "(" <> typed value <> ")")

renderClientRecord
  :: ModuleContext
  -> M.Expr
  -> [(String, Operand)]
  -> Codegen Operand
renderClientRecord context source fields = do
  body <- foldM appendField
    (stringOperand context (ByteString8.pack "{"))
    (zip [0 :: Int ..] fields)
  lowerStringConcatOperands source body
    (stringOperand context (ByteString8.pack "}"))
  where
    appendField rendered (index, (name, value)) = do
      separated <- if index == 0
        then pure rendered
        else lowerStringConcatOperands source rendered
          (stringOperand context (ByteString8.pack ","))
      named <- lowerStringConcatOperands source separated
        (stringOperand context (ByteString8.pack ("\"" <> name <> "\":")))
      lowerStringConcatOperands source named value

renderClientTagged
  :: ModuleContext
  -> M.Expr
  -> Int
  -> Maybe Operand
  -> Codegen Operand
renderClientTagged context source tag payload = do
  withTag <- lowerStringConcatOperands source
    (stringOperand context (ByteString8.pack "({tag:"))
    (stringOperand context (ByteString8.pack (show tag)))
  withPayloadName <- lowerStringConcatOperands source withTag
    (stringOperand context (ByteString8.pack ",payload:"))
  withPayload <- lowerStringConcatOperands source withPayloadName
    (case payload of
      Just value -> value
      Nothing -> stringOperand context (ByteString8.pack "null"))
  lowerStringConcatOperands source withPayload
    (stringOperand context (ByteString8.pack "})"))

lowerClientListCapture
  :: ModuleContext
  -> M.Expr
  -> Map.Map M.GlobalId String
  -> M.Type
  -> M.Type
  -> Operand
  -> Codegen Operand
lowerClientListCapture context source recursive listType element value = do
  helper <- freshHelperName "client_capture_list"
  let initial = initialCodegenState helper []
      body = do
        let argument = Operand Ptr "%argument"
            payloadSourceType = Located (locatedSpan source)
              (M.TRecord [("1", element), ("2", listType)])
        payloadType <- liftEither (lowerTypeAt (locatedSpan source) payloadSourceType)
        lowerTaggedUrlEncode context source argument
          [ (0, renderClientTagged context source 0 Nothing)
          , (1, do
              payload <- loadTaggedExprPayload source argument payloadType
              case payloadType of
                Record [(headName, headType), (tailName, tailType)] -> do
                  headValue <- emitResult headType
                    ("extractvalue " <> renderType payloadType <> " " <> operandText payload <> ", 0")
                  tailValue <- emitResult tailType
                    ("extractvalue " <> renderType payloadType <> " " <> operandText payload <> ", 1")
                  headEncoded <- lowerClientCaptureWith context source recursive element headValue
                  tailEncoded <- callUrlEncodeHelper helper tailValue
                  encoded <- renderClientRecord context source
                    [(headName, headEncoded), (tailName, tailEncoded)]
                  renderClientTagged context source 1 (Just encoded)
                _ -> failCodegen source "llvm-html-client-capture"
                  "Native browser list capture has an invalid payload")
          ]
  (result, final) <- liftEither (runStateT body initial)
  addHelperDefinition helper Ptr Ptr result final
  callUrlEncodeHelper helper value

lowerClientDatatypeCapture
  :: ModuleContext
  -> M.Expr
  -> Map.Map M.GlobalId String
  -> M.GlobalId
  -> Operand
  -> Codegen Operand
lowerClientDatatypeCapture context source recursive identifier value = do
  datatypeInfo <- case Map.lookup identifier (moduleDatatypes context) of
    Just found -> pure found
    Nothing -> failCodegen source "llvm-html-client-capture"
      "Native browser capture refers to an unknown datatype"
  helper <- freshHelperName "client_capture_datatype"
  let recursive' = Map.insert identifier helper recursive
      initial = initialCodegenState helper []
      body = do
        let argument = Operand Ptr "%argument"
        lowerTaggedUrlEncode context source argument
          [ (tag, case payloadSourceType of
              Nothing -> renderClientTagged context source tag Nothing
              Just payloadType -> do
                payloadLlvm <- liftEither (lowerTypeAt (locatedSpan source) payloadType)
                payload <- loadTaggedExprPayload source argument payloadLlvm
                encoded <- lowerClientCaptureWith context source recursive' payloadType payload
                renderClientTagged context source tag (Just encoded))
          | (tag, (_, _, payloadSourceType)) <-
              zip [0 :: Int ..] (datatypeConstructors datatypeInfo)
          ]
  (result, final) <- liftEither (runStateT body initial)
  addHelperDefinition helper Ptr Ptr result final
  callUrlEncodeHelper helper value

htmlAttributeName :: String -> String
htmlAttributeName name = case name of
  "Action" -> "formaction"
  "Link" -> "href"
  "Typ" -> "type"
  "Nam" -> "name"
  _ -> concatMap normalize name
  where
    normalize '_' = "-"
    normalize character = [toLower character]

htmlTagName :: M.Expr -> Maybe String
htmlTagName expression = htmlElementName <$> htmlBasisTagName expression

htmlBasisTagName :: M.Expr -> Maybe String
htmlBasisTagName expression = case locatedValue expression of
  M.EApp function _ -> htmlBasisTagName function
  M.EFfi "Basis" name _
    | name `notElem` ["tag", "join", "cdata", "null", "noStyle"] -> Just name
  M.EFfi _ name _ -> Just name
  _ -> Nothing

htmlElementName :: String -> String
htmlElementName name = case name of
  "tabl" -> "table"
  "cselect" -> "select"
  "coption" -> "option"
  "ctextarea" -> "textarea"
  _ | name `elem` inputControlNames -> "input"
  _ -> map toLower name

htmlControlInfo :: M.Expr -> Maybe (String, Maybe String)
htmlControlInfo expression = case locatedValue expression of
  M.EApp function _ -> htmlControlInfo function
  M.EFfi "Basis" name arguments
    | name `elem` serverInputControlNames -> do
        fieldName <- lastStaticName arguments
        pure (htmlInputType name, Just fieldName)
    | name `elem` clientInputControlNames -> Just (htmlInputType name, Nothing)
  _ -> Nothing
  where
    lastStaticName arguments = case reverse arguments of
      M.StaticName name : _ -> Just name
      _ -> Nothing

htmlContainerControlName :: String -> M.Expr -> Maybe String
htmlContainerControlName element expression
  | element `elem` ["textarea", "select"] = go expression
  | otherwise = Nothing
  where
    go current = case locatedValue current of
      M.EApp function _ -> go function
      M.EFfi "Basis" _ arguments -> case reverse arguments of
        M.StaticName name : _ -> Just name
        _ -> Nothing
      _ -> Nothing

htmlInputType :: String -> String
htmlInputType name = case name of
  "textbox" -> "text"
  "ctextbox" -> "text"
  "url_" -> "url"
  "timeInput" -> "time"
  "ctime" -> "time"
  "datetime_local" -> "datetime-local"
  "cdatetime_local" -> "datetime-local"
  "upload" -> "file"
  _ | 'c' : control <- name, name `elem` clientInputControlNames -> control
  _ -> name

serverInputControlNames :: [String]
serverInputControlNames =
  [ "textbox", "password", "email", "search", "url_", "tel", "color", "hidden", "checkbox"
  , "number", "range", "date", "datetime", "datetime_local", "month", "week"
  , "timeInput", "upload"
  ]

clientInputControlNames :: [String]
clientInputControlNames =
  [ "ctextbox", "cpassword", "cemail", "csearch", "curl", "ctel", "ccolor"
  , "cnumber", "crange", "cdate", "cdatetime", "cdatetime_local", "cmonth", "cweek"
  , "ctime", "ccheckbox", "cradio"
  ]

inputControlNames :: [String]
inputControlNames = serverInputControlNames <> clientInputControlNames

clientControlKind :: String -> Maybe String
clientControlKind name
  | name `elem`
      [ "ctextbox", "cpassword", "cemail", "csearch", "curl", "ctel", "ccolor"
      , "cdate", "cdatetime", "cdatetime_local", "cmonth", "cweek", "ctime"
      , "ctextarea", "cselect"
      ] = Just "string"
  | name `elem` ["cnumber", "crange"] = Just "option-float"
  | name == "ccheckbox" = Just "bool"
  | name == "cradio" = Just "radio"
  | otherwise = Nothing

htmlTagFragments :: String -> (String, String, String)
htmlTagFragments name = case name of
  "submit" -> ("<input type=\"submit\"", " />", "")
  _ | name `elem` htmlVoidTags -> ("<" <> name, " />", "")
  _ -> ("<" <> name, ">", "</" <> name <> ">")

htmlVoidTags :: [String]
htmlVoidTags =
  [ "area", "base", "br", "col", "embed", "hr", "img", "input", "link"
  , "meta", "param", "source", "track", "wbr"
  ]

htmlSafeExpression :: M.Expr -> Bool
htmlSafeExpression expression = case locatedValue expression of
  M.EPrim (PrimString HtmlString _) -> True
  M.EStrcat left right -> htmlSafeExpression left && htmlSafeExpression right
  _ -> False

lowerSleep :: ModuleContext -> M.Expr -> M.Expr -> Codegen Operand
lowerSleep context source duration = lowerExpr context duration >>= lowerSleepOperand source

lowerSleepOperand :: M.Expr -> Operand -> Codegen Operand
lowerSleepOperand source duration = do
  ensureOperand source I64 duration
  emitInstruction ("call void @vr_runtime_sleep_ms(" <> typed duration <> ")")
  pure (Operand I8 "0")

lowerReceive :: ModuleContext -> M.Expr -> M.Expr -> M.Type -> Codegen Operand
lowerReceive context source channel typ = do
  channel' <- lowerExpr context channel
  ensureOperand source Ptr channel'
  resultType <- liftEither (lowerTypeAt (locatedSpan source) typ)
  boxed <- emitResult Ptr ("call ptr @vr_runtime_channel_recv(" <> typed channel' <> ")")
  value <- emitResult resultType ("load " <> renderType resultType <> ", ptr " <> operandText boxed)
  emitInstruction ("call void @free(" <> typed boxed <> ")")
  pure value

lowerSpawn :: ModuleContext -> M.Expr -> M.Expr -> Codegen Operand
lowerSpawn context _source action = do
  captures <- gets codegenLocals
  prefix <- gets codegenHelperPrefix
  helperIndex <- gets codegenNextHelper
  modify' (\state -> state {codegenNextHelper = helperIndex + 1})
  let helperName = prefix <> "_spawn_" <> show helperIndex
      captureType = Record [("capture" <> show index, operandType value) | (index, value) <- zip [0 :: Int ..] captures]
  environment <- case captures of
    [] -> pure (Operand Ptr "null")
    _ -> do
      -- A spawned action may outlive the request arena that creates it.
      allocation <- allocatePersistent captureType
      forM_ (zip [0 :: Int ..] captures) $ \(index, value) -> do
        address <- emitResult Ptr
          ("getelementptr inbounds " <> renderType captureType <> ", ptr " <> operandText allocation <> ", i32 0, i32 " <> show index)
        emitInstruction ("store " <> typed value <> ", ptr " <> operandText address)
      pure allocation
  let helperInitial = initialCodegenState helperName []
      buildHelper = do
        restored <- forM (zip [0 :: Int ..] captures) $ \(index, value) -> do
          address <- emitResult Ptr
            ("getelementptr inbounds " <> renderType captureType <> ", ptr %environment, i32 0, i32 " <> show index)
          emitResult (operandType value) ("load " <> renderType (operandType value) <> ", ptr " <> operandText address)
        modify' (\state -> state {codegenLocals = restored})
        actionValue <- lowerExpr context action
        _ <- runTransactionOperand context action actionValue
        pure ()
  helperFinal <- liftEither (execStateT buildHelper helperInitial)
  let helperInstructions = reverse (codegenInstructions helperFinal)
      helperDefinition = unlines
        ([ "define internal void @" <> helperName <> "(ptr %environment) {"
         , "entry:"
         , "  call void @vr_runtime_database_transaction_begin()"
         ]
          <> map ("  " <>) helperInstructions
          <> ["  call void @vr_runtime_database_transaction_finish(i1 true)"]
          <> ["  call void @free(ptr %environment)" | not (null captures)]
          <> ["  ret void", "}", ""])
      generated = reverse (codegenHelpers helperFinal) <> [helperDefinition]
  modify' (\state -> state {codegenHelpers = reverse generated <> codegenHelpers state})
  emitInstruction ("call void @vr_runtime_spawn(ptr @" <> helperName <> ", " <> typed environment <> ")")
  pure (Operand I8 "0")

runDeferredTransaction :: ModuleContext -> M.Expr -> Deferred -> Codegen Operand
runDeferredTransaction context source deferred = do
  value <- force context deferred
  runTransactionOperand context source value

runTransactionOperand :: ModuleContext -> M.Expr -> Operand -> Codegen Operand
runTransactionOperand context source value = case operandType value of
  Function I8 _ -> applyClosure context source value (Lowered (Operand I8 "0"))
  _ -> pure value

lowerError :: ModuleContext -> M.Expr -> M.Expr -> M.Type -> Codegen Operand
lowerError context source message typ = do
  message' <- lowerExpr context message
  ensureOperand source Ptr message'
  -- Failure never returns, but the unreachable placeholder must still retain
  -- its declared type. In particular, a transaction-valued error remains a
  -- function here so an enclosing bind can lower its (unreachable) application.
  resultType <- liftEither (lowerTypeAt (locatedSpan source) typ)
  emitInstruction ("call void @vr_runtime_fail(" <> typed message' <> ")")
  pure (zeroOperand resultType)

staticResultType :: M.Expr -> [M.StaticArg] -> Codegen LlvmType
staticResultType source arguments =
  staticResultMonoType source arguments
    >>= liftEither . lowerTypeAt (locatedSpan source)

staticResultMonoType :: M.Expr -> [M.StaticArg] -> Codegen M.Type
staticResultMonoType source arguments = case arguments of
  argument : _ -> liftEither (staticMonoTypeAt (locatedSpan source) argument)
  [] -> failCodegen source "llvm-static-type" "Intrinsic is missing its resolved result type"

lowerStaticTypeAt :: Span -> M.StaticArg -> Either Diagnostic LlvmType
lowerStaticTypeAt at argument = staticMonoTypeAt at argument >>= lowerTypeAt at

staticMonoTypeAt :: Span -> M.StaticArg -> Either Diagnostic M.Type
staticMonoTypeAt at argument = Located at <$> case argument of
  M.StaticType typ -> pure (locatedValue typ)
  M.StaticRow fields -> M.TRecord <$> mapM staticField fields
  M.StaticTuple elements -> M.TRecord <$> mapM staticTupleField (zip [1 :: Int ..] elements)
  M.StaticFfi "Basis" "unit" [] -> pure (M.TRecord [])
  M.StaticFfi "Basis" "option" [element] -> M.TOption <$> staticMonoTypeAt at element
  M.StaticFfi "Basis" "list" [element] -> M.TList <$> staticMonoTypeAt at element
  M.StaticFfi "Basis" "source" [_] -> pure M.TSource
  M.StaticFfi "Basis" "signal" [element] -> M.TSignal <$> staticMonoTypeAt at element
  M.StaticFfi "Basis" "transaction" [result] ->
    M.TFun (Located at (M.TRecord [])) <$> staticMonoTypeAt at result
  M.StaticFfi moduleName name _ -> pure (M.TFfi moduleName name)
  _ -> backendFailureAt at "llvm-static-type"
    "Intrinsic retained a static type that the native backend cannot represent"
  where
    staticField (M.StaticName name, value) = (,) name <$> staticMonoTypeAt at value
    staticField _ = backendFailureAt at "llvm-static-type"
      "Static record type retained a non-name field"
    staticTupleField (index, value) = (,) (show index) <$> staticMonoTypeAt at value

-- ERecv already stores a Mono type.  Calls that still arrive as Basis.recv
-- carry the same type as a StaticArg; this small conversion lets both forms
-- share one load path without reconstructing source-level constructors.
llvmTypeToMonoType :: Span -> LlvmType -> M.Type
llvmTypeToMonoType at typ = Located at $ case typ of
  I1 -> M.TFfi "Basis" "bool"
  I8 -> M.TRecord []
  I32 -> M.TFfi "Basis" "char"
  I64 -> M.TFfi "Basis" "int"
  F64 -> M.TFfi "Basis" "float"
  Ptr -> M.TFfi "Basis" "string"
  Function domain range -> M.TFun (llvmTypeToMonoType at domain) (llvmTypeToMonoType at range)
  Record fields -> M.TRecord [(name, llvmTypeToMonoType at fieldType) | (name, fieldType) <- fields]

zeroOperand :: LlvmType -> Operand
zeroOperand typ = Operand typ $ case typ of
  I1 -> "0"
  I8 -> "0"
  I32 -> "0"
  I64 -> "0"
  F64 -> "0.0"
  Ptr -> "null"
  Function {} -> "null"
  Record {} -> "zeroinitializer"

deferredExpression :: M.Expr -> Deferred -> Codegen M.Expr
deferredExpression _ (DeferredExpr expression) = pure expression
deferredExpression source (Lowered _) = failCodegen source "llvm-continuation" "Transaction continuation was evaluated before direct application"

lowerNumeric :: M.Expr -> String -> Operand -> Operand -> Codegen Operand
lowerNumeric source operator left right = case operandType left of
  I64 | operator `elem` ["div", "mod"]
      , Just divisor <- readMaybe (operandText right) :: Maybe Int64
      , divisor /= 0 && divisor /= -1 ->
          -- A nonzero constant other than -1 cannot divide by zero or cause
          -- signed division overflow, even for INT64_MIN. Exposing it to LLVM
          -- permits constant-divisor strength reduction. Unknown, zero, and
          -- -1 divisors keep the existing runtime path and its behavior.
          emitResult I64 ((if operator == "div" then "sdiv" else "srem")
            <> " i64 " <> operandText left <> ", " <> operandText right)
      | operator == "div" -> runtime I64 "vr_runtime_div_int"
      | operator == "mod" -> runtime I64 "vr_runtime_mod_int"
      | operator == "pow" -> runtime I64 "vr_runtime_pow_int"
      | otherwise -> emitResult I64 (integerInstruction operator <> " i64 " <> operandText left <> ", " <> operandText right)
  F64 | operator == "pow" -> runtime F64 "vr_runtime_pow_float"
      | otherwise -> emitResult F64 (floatInstruction operator <> " double " <> operandText left <> ", " <> operandText right)
  _ -> failCodegen source "llvm-numeric-type" ("Numeric intrinsic received " <> renderType (operandType left))
  where
    runtime resultType function = emitResult resultType
      ("call " <> renderType resultType <> " @" <> function <> "(" <> typed left <> ", " <> typed right <> ")")
    integerInstruction name = case name of
      "plus" -> "add"; "minus" -> "sub"; _ -> "mul"
    floatInstruction name = case name of
      "plus" -> "fadd"; "minus" -> "fsub"; "times" -> "fmul"; "div" -> "fdiv"; _ -> "frem"

lowerUnaryOperator :: ModuleContext -> M.Expr -> String -> M.Expr -> Codegen Operand
lowerUnaryOperator context source operator value = do
  value' <- lowerExpr context value
  case (operator, operandType value') of
    ("!", I1) -> emitResult I1 ("xor i1 " <> operandText value' <> ", true")
    ("-", I64) -> emitResult I64 ("sub i64 0, " <> operandText value')
    ("-", F64) -> emitResult F64 ("fneg double " <> operandText value')
    _ -> failCodegen source "llvm-unary" ("Unsupported unary operator " <> operator <> " for " <> renderType (operandType value'))

lowerBinaryOperator :: ModuleContext -> M.Expr -> String -> M.Expr -> M.Expr -> Codegen Operand
lowerBinaryOperator context source operator left right = do
  left' <- lowerExpr context left
  right' <- lowerExpr context right
  ensureSame source left' right'
  case operator of
    "+" -> lowerNumeric source "plus" left' right'
    "-" -> lowerNumeric source "minus" left' right'
    "*" -> lowerNumeric source "times" left' right'
    "/" -> lowerNumeric source "div" left' right'
    "%" -> lowerNumeric source "mod" left' right'
    "powl" -> lowerNumeric source "pow" left' right'
    "fdiv" -> lowerNumeric source "div" left' right'
    "fmod" -> lowerNumeric source "mod" left' right'
    "powf" -> lowerNumeric source "pow" left' right'
    "==" -> lowerComparison source [] "eq" left' right'
    "!strcmp" -> do
      ensureOperand source Ptr left'
      comparison <- emitResult I32 ("call i32 @strcmp(" <> typed left' <> ", " <> typed right' <> ")")
      emitResult I1 ("icmp eq i32 " <> operandText comparison <> ", 0")
    "strcmp" -> do
      ensureOperand source Ptr left'
      comparison <- emitResult I32 ("call i32 @strcmp(" <> typed left' <> ", " <> typed right' <> ")")
      emitResult I64 ("sext i32 " <> operandText comparison <> " to i64")
    "<" -> lowerComparison source [] "lt" left' right'
    "<=" -> lowerComparison source [] "le" left' right'
    _ -> failCodegen source "llvm-binary" ("Unsupported binary operator " <> operator)

lowerComparison :: M.Expr -> [M.StaticArg] -> String -> Operand -> Operand -> Codegen Operand
lowerComparison source staticArguments operator left right = case operandType left of
  I64 -> emitResult I1 ("icmp " <> integerPredicate operator <> " i64 " <> operandText left <> ", " <> operandText right)
  I32 -> emitResult I1 ("icmp " <> integerPredicate operator <> " i32 " <> operandText left <> ", " <> operandText right)
  I8 -> emitResult I1 ("icmp " <> integerPredicate operator <> " i8 " <> operandText left <> ", " <> operandText right)
  I1 -> emitResult I1 ("icmp " <> boolPredicate operator <> " i1 " <> operandText left <> ", " <> operandText right)
  F64 -> emitResult I1 ("fcmp " <> floatPredicate operator <> " double " <> operandText left <> ", " <> operandText right)
  Ptr | isStringStatic staticArguments -> do
    ordering <- emitResult I32 ("call i32 @strcmp(" <> typed left <> ", " <> typed right <> ")")
    emitResult I1 ("icmp " <> stringPredicate operator <> " i32 " <> operandText ordering <> ", 0")
  _ -> failCodegen source "llvm-comparison-type" ("Comparison intrinsic received " <> renderType (operandType left))
  where
    integerPredicate name = case name of
      "eq" -> "eq"; "neq" -> "ne"; "lt" -> "slt"; "le" -> "sle"; "gt" -> "sgt"; _ -> "sge"
    boolPredicate name = case name of
      "eq" -> "eq"; "neq" -> "ne"; "lt" -> "ult"; "le" -> "ule"; "gt" -> "ugt"; _ -> "uge"
    floatPredicate name = case name of
      "eq" -> "oeq"; "neq" -> "une"; "lt" -> "olt"; "le" -> "ole"; "gt" -> "ogt"; _ -> "oge"
    stringPredicate name = case name of
      "eq" -> "eq"; "neq" -> "ne"; "lt" -> "slt"; "le" -> "sle"; "gt" -> "sgt"; _ -> "sge"

isStringStatic :: [M.StaticArg] -> Bool
isStringStatic arguments = case arguments of
  M.StaticFfi "Basis" name _ : _
    | name `elem` ["string", "url", "css_class", "id", "queryString"] -> True
  _ -> False

isBasisStatic :: String -> [M.StaticArg] -> Bool
isBasisStatic wanted arguments = case arguments of
  M.StaticFfi "Basis" actual _ : _ -> wanted == actual
  _ -> False

lowerStringConcat :: ModuleContext -> M.Expr -> M.Expr -> M.Expr -> Codegen Operand
lowerStringConcat context source left right = do
  left' <- lowerExpr context left
  right' <- lowerExpr context right
  lowerStringConcatOperands source left' right'

lowerStringConcatOperands :: M.Expr -> Operand -> Operand -> Codegen Operand
lowerStringConcatOperands source left right
  | staticEmptyString left = ensureOperand source Ptr right >> pure right
  | staticEmptyString right = ensureOperand source Ptr left >> pure left
  | otherwise = do
      ensureOperand source Ptr left
      ensureOperand source Ptr right
      leftLength <- emitResult I64 ("call i64 @strlen(" <> typed left <> ")")
      rightLength <- emitResult I64 ("call i64 @strlen(" <> typed right <> ")")
      contentLength <- emitResult I64 ("add i64 " <> operandText leftLength <> ", " <> operandText rightLength)
      allocationLength <- emitResult I64 ("add i64 " <> operandText contentLength <> ", 1")
      rightCopyLength <- emitResult I64 ("add i64 " <> operandText rightLength <> ", 1")
      destination <- emitResult Ptr ("call ptr @vr_runtime_alloc(i64 " <> operandText allocationLength <> ")")
      _ <- emitResult Ptr
        ("call ptr @memcpy(ptr " <> operandText destination <> ", " <> typed left <> ", i64 " <> operandText leftLength <> ")")
      tailAddress <- emitResult Ptr
        ("getelementptr inbounds i8, ptr " <> operandText destination <> ", i64 " <> operandText leftLength)
      _ <- emitResult Ptr
        ("call ptr @memcpy(ptr " <> operandText tailAddress <> ", " <> typed right <> ", i64 " <> operandText rightCopyLength <> ")")
      pure destination

-- Global string constants include their trailing NUL, so a one-byte global
-- is necessarily the empty string.  Avoiding concatenation with it matters
-- for generated HTML: absent class, style, dynamic, and record attributes
-- otherwise created a cascade of request-arena allocations for every tag.
staticEmptyString :: Operand -> Bool
staticEmptyString operand = operandType operand == Ptr
  && "getelementptr inbounds ([1 x i8]" `isInfixOf` operandText operand

lowerPrimitive :: ModuleContext -> M.Expr -> Primitive -> Codegen Operand
lowerPrimitive context source = primitiveOperand context (locatedSpan source)

primitiveOperand :: ModuleContext -> Span -> Primitive -> Codegen Operand
primitiveOperand context at primitive = case primitive of
  PrimInt value -> pure (Operand I64 (showInt64 value))
  PrimFloat value -> pure (Operand F64 (show value))
  PrimChar value -> pure (Operand I32 (showWord8 value))
  PrimString _ bytes -> case Map.lookup bytes (moduleStrings context) of
    Just (index, size) -> pure (Operand Ptr ("getelementptr inbounds ([" <> show size <> " x i8], ptr @vr_str_" <> show index <> ", i64 0, i64 0)"))
    Nothing -> lift (Left (diagnostic BackendPhase "llvm-string" at "String literal was absent from the module string table"))

lowerTypeAt :: Span -> M.Type -> Either Diagnostic LlvmType
lowerTypeAt at source = case locatedValue source of
  M.TFfi "Basis" "int" -> pure I64
  M.TFfi "Basis" "float" -> pure F64
  M.TFfi "Basis" "bool" -> pure I1
  M.TFfi "Basis" "char" -> pure I32
  M.TFfi "Basis" "string" -> pure Ptr
  M.TFfi "Basis" "channel" -> pure Ptr
  M.TFfi "Basis" "postBody" -> pure Ptr
  M.TFfi "Basis" "postField" -> pure Ptr
  M.TFfi "Basis" _ -> pure Ptr
  M.TFfi _ _ -> pure Ptr
  M.TRecord [] -> pure I8
  M.TRecord fields -> Record <$> mapM (\(name, typ) -> do lowered <- lowerTypeAt at typ; pure (name, lowered)) fields
  M.TDatatype {} -> pure Ptr
  M.TOption {} -> pure Ptr
  M.TList {} -> pure Ptr
  M.TSource -> pure Ptr
  M.TSignal {} -> pure Ptr
  M.TFun domain range -> Function <$> lowerTypeAt at domain <*> lowerTypeAt at range

collectApplications :: M.Expr -> (M.Expr, [M.Expr])
collectApplications = go []
  where
    go arguments expression = case locatedValue expression of
      M.EApp function argument -> go (argument : arguments) function
      _ -> (expression, arguments)

declarationStrings :: M.Decl -> [ByteString.ByteString]
declarationStrings source = case locatedValue source of
  M.DVal _ _ _ expression _ -> expressionStrings expression
  M.DValRec bindings -> concatMap (expressionStrings . fourth) bindings
  M.DTask schedule body -> expressionStrings schedule <> expressionStrings body
  M.DTable _ _ primary constraints -> expressionStrings primary <> expressionStrings constraints
  M.DView _ _ expression -> expressionStrings expression
  M.DIndexDynamic table modes -> expressionStrings table <> expressionStrings modes
  M.DPolicy policy -> policyStrings policy
  M.DPolicyRaw expression -> expressionStrings expression
  _ -> []
  where fourth (_, _, _, value, _) = value

declarationTypeStrings :: M.Decl -> [ByteString.ByteString]
declarationTypeStrings source = case locatedValue source of
  M.DVal _ _ typ _ _ -> typeStrings typ
  M.DValRec bindings -> concatMap (typeStrings . bindingType) bindings
  M.DExport _ _ _ arguments result _ -> concatMap typeStrings (result : arguments)
  M.DTable _ fields _ _ -> concatMap fieldStrings fields
  M.DView _ fields _ -> concatMap fieldStrings fields
  _ -> []
  where
    bindingType (_, _, typ, _, _) = typ
    fieldStrings (name, typ) =
      map ByteString8.pack (name : sqlIdentifierVariants name) <> typeStrings typ

typeStrings :: M.Type -> [ByteString.ByteString]
typeStrings typ = case locatedValue typ of
  M.TFun domain range -> typeStrings domain <> typeStrings range
  M.TRecord fields ->
    [ fragment
    | (name, _) <- fields
    , fragment <- map ByteString8.pack (name : sqlIdentifierVariants name <> ["\"" <> name <> "\":"])
    ] <> concatMap (typeStrings . snd) fields
  M.TOption element -> typeStrings element
  M.TList element -> typeStrings element
  M.TSignal element -> typeStrings element
  _ -> []

policyStrings :: M.Policy -> [ByteString.ByteString]
policyStrings policy = case policy of
  M.PolicyClient expression -> expressionStrings expression
  M.PolicyInsert expression -> expressionStrings expression
  M.PolicyDelete expression -> expressionStrings expression
  M.PolicyUpdate expression -> expressionStrings expression
  M.PolicySequence expression -> expressionStrings expression

expressionStrings :: M.Expr -> [ByteString.ByteString]
expressionStrings source = expressionStringsOnto source []

-- Preserve traversal/first-occurrence order without copying a subtree's
-- collected strings at each ancestor of an application or concatenation.
expressionStringsOnto :: M.Expr -> [ByteString.ByteString] -> [ByteString.ByteString]
expressionStringsOnto source rest = direct <> children
  where
    direct = primitiveStrings <> htmlStrings <> intrinsicStrings <> clientTypeStrings
    primitiveStrings = case locatedValue source of
      M.EPrim (PrimString _ bytes) -> [bytes]
      _ -> []
    htmlStrings = tagStrings <> attributeStrings
    tagStrings = case htmlTagApplication source of
      Just name -> let (opening, ending, closing) = htmlTagFragments name
                   in map ByteString8.pack [opening, ending, opening <> ending, closing]
      Nothing -> []
    attributeStrings = case locatedValue source of
      M.ERecord fields -> concatMap attributeFieldStrings fields
      _ -> []
    attributeFieldStrings (M.StaticName name, _, _) =
      [ ByteString8.pack (" " <> htmlAttributeName name <> "=\"")
      , ByteString8.pack (" " <> htmlAttributeName name)
      , ByteString8.pack "\""
      ]
    attributeFieldStrings _ = []
    intrinsicStrings = case locatedValue source of
      M.EFfi "Basis" name arguments -> controlString name <> concatMap staticArgumentStrings arguments
      M.EFfiApp "Basis" name arguments _ -> controlString name <> concatMap staticArgumentStrings arguments
      _ -> []
    clientTypeStrings = case locatedValue source of
      M.EJavaScript (M.JavaScriptSource typ) _ -> typeStrings typ
      M.ERecord fields -> concatMap (typeStrings . fieldType) fields
      _ -> []
    controlString name
      | name `elem` inputControlNames = [ByteString8.pack (htmlInputType name)]
      | otherwise = []
    children = case locatedValue source of
      M.ECon _ _ payload -> maybe rest (\value -> collect value rest) payload
      M.ESome _ value -> collect value rest
      M.EFfiApp _ _ _ arguments -> foldr (collect . fst) rest arguments
      M.EApp function argument -> collect function (collect argument rest)
      M.EAbs _ _ _ body -> collect body rest
      M.EStaticApp function _ -> collect function rest
      M.EUnop _ value -> collect value rest
      M.EBinop _ _ left right -> collect left (collect right rest)
      M.ERecord fields -> foldr (collect . fieldValue) rest fields
      M.EField record _ -> collect record rest
      M.ERecordConcat left right -> collect left (collect right rest)
      M.ERecordCut record _ -> collect record rest
      M.ECase scrutinee branches _ _ -> collect scrutinee
        (foldr (\(pattern', body) tail' -> patternStrings pattern' <> collect body tail') rest branches)
      M.EStrcat left right -> collect left (collect right rest)
      M.EError value _ -> collect value rest
      M.EReturnBlob content value _ -> maybe id collect content (collect value rest)
      M.ERedirect value _ -> collect value rest
      M.EWrite value -> collect value rest
      M.ESeq first second -> collect first (collect second rest)
      M.ELet _ _ value body -> collect value (collect body rest)
      M.EClosure _ captures -> foldr collect rest captures
      M.EQuery _ _ _ query body initial -> collect query (collect body (collect initial rest))
      M.EDml value _ -> collect value rest
      M.ENextval value -> collect value rest
      M.ESetval sequence' value -> collect sequence' (collect value rest)
      M.EUnurlify value _ _ -> collect value rest
      M.EJavaScript _ value -> collect value rest
      M.ESignalReturn value -> collect value rest
      M.ESignalBind signal continuation -> collect signal (collect continuation rest)
      M.ESqlCache _ typ keys action ->
        typeStrings typ <> foldr collect (collect action rest) keys
      M.ESqlCacheFlush typ flushes action ->
        typeStrings typ <> foldr (\key -> maybe id collect key) (collect action rest)
          [ key
          | flush <- flushes
          , key <- M.sqlCacheFlushKeys flush
          ]
      M.ESignalSource value -> collect value rest
      M.EServerCall call _ _ _ -> collect call rest
      M.ERecv channel _ -> collect channel rest
      M.ESleep value -> collect value rest
      M.ESpawn value -> collect value rest
      _ -> rest
    collect = expressionStringsOnto
    fieldValue (_, value, _) = value
    fieldType (_, _, typ) = typ

patternStrings :: M.Pattern -> [ByteString.ByteString]
patternStrings pattern' = case locatedValue pattern' of
  M.PPrim (PrimString _ bytes) -> [bytes]
  M.PCon _ _ nested -> maybe [] patternStrings nested
  M.PRecord fields -> concatMap (patternStrings . nestedPattern) fields
  M.PSome _ nested -> patternStrings nested
  _ -> []
  where
    nestedPattern (_, nested, _) = nested

staticArgumentStrings :: M.StaticArg -> [ByteString.ByteString]
staticArgumentStrings argument = case argument of
  M.StaticType typ -> typeStrings typ
  M.StaticName name -> map ByteString8.pack (name : sqlIdentifierVariants name)
  M.StaticRow fields -> concatMap (\(name, value) -> staticArgumentStrings name <> staticArgumentStrings value) fields
  M.StaticTuple elements -> concatMap staticArgumentStrings elements
  M.StaticFfi _ _ arguments -> concatMap staticArgumentStrings arguments
  M.StaticLambda body -> staticArgumentStrings body
  M.StaticApply function value -> staticArgumentStrings function <> staticArgumentStrings value
  M.StaticProject tuple _ -> staticArgumentStrings tuple
  M.StaticConcat left right -> staticArgumentStrings left <> staticArgumentStrings right
  _ -> []

htmlTagApplication :: M.Expr -> Maybe String
htmlTagApplication expression =
  let (function, arguments) = collectApplications expression
   in case (locatedValue function, reverse arguments) of
        (M.EFfi "Basis" "tag" _, _child : descriptor : _) -> htmlTagName descriptor
        -- Fuse writes the opening tag separately from its child. Its prefix
        -- is still a generated string literal, even when no unsplit occurrence
        -- of the tag remains to populate the string table.
        (M.EFfi "Basis" "__vr_tag_open" _, descriptor : _) -> htmlTagName descriptor
        (M.EFfiApp "Basis" "tag" _ values, []) -> case reverse values of
          _child : (descriptor, _) : _ -> htmlTagName descriptor
          _ -> Nothing
        (M.EFfiApp "Basis" "__vr_tag_open" _ values, []) -> case reverse values of
          (descriptor, _) : _ -> htmlTagName descriptor
          _ -> Nothing
        _ -> Nothing

renderStringDefinition :: ByteString.ByteString -> (Int, Int) -> ByteStringBuilder.Builder
renderStringDefinition bytes (index, size) =
  ByteStringBuilder.string8 "@vr_str_"
    <> ByteStringBuilder.intDec index
    <> ByteStringBuilder.string8 " = private unnamed_addr constant ["
    <> ByteStringBuilder.intDec size
    <> ByteStringBuilder.string8 " x i8] c\""
    <> llvmBytes bytes
    <> ByteStringBuilder.string8 "\\00\", align 1"

llvmBytes :: ByteString.ByteString -> ByteStringBuilder.Builder
llvmBytes bytes
  | ByteString.null bytes = mempty
  | otherwise =
      let (safe, escaped) = ByteString.break needsEscape bytes
       in ByteStringBuilder.byteString safe <> case ByteString.uncons escaped of
            Nothing -> mempty
            Just (byte, rest) -> escapedByte byte <> llvmBytes rest
  where
    needsEscape byte = byte < 0x20 || byte > 0x7e || byte == 0x22 || byte == 0x5c
    escapedByte byte = ByteStringBuilder.char8 '\\'
      <> ByteStringBuilder.word8 (hexDigit (byte `div` 16))
      <> ByteStringBuilder.word8 (hexDigit (byte `mod` 16))
    hexDigit nibble
      | nibble < 10 = 0x30 + nibble
      | otherwise = 0x37 + nibble

llvmGlobalName :: String -> M.GlobalId -> String
llvmGlobalName name identifier = "@vr_g" <> show (M.unGlobalId identifier) <> "_" <> sanitize name

renderForeignCodecDeclarations :: (String, String) -> [String]
renderForeignCodecDeclarations (moduleName, typeName) =
  [ "declare ptr @" <> foreignCodecEncodeSymbol moduleName typeName <> "(ptr, ptr)"
  , "declare ptr @" <> foreignCodecDecodeSymbol moduleName typeName <> "(ptr, ptr, ptr)"
  ]

renderForeignConstructorDeclarations :: Server.ForeignConstructor -> [String]
renderForeignConstructorDeclarations constructor =
  [ "declare ptr @vr_foreign_constructor_make_" <> identifier <> "(ptr, ptr)"
  , "declare i32 @vr_foreign_constructor_match_" <> identifier <> "(ptr)"
  ] <> case Server.foreignConstructorPayload constructor of
    Nothing -> []
    Just _ ->
      ["declare ptr @vr_foreign_constructor_payload_" <> identifier <> "(ptr, ptr)"]
  where
    identifier = show (Server.foreignConstructorId constructor)

foreignCodecEncodeSymbol :: String -> String -> String
foreignCodecEncodeSymbol moduleName typeName =
  "vr_codec_encode_" <> sanitize moduleName <> "_" <> sanitize typeName

foreignCodecDecodeSymbol :: String -> String -> String
foreignCodecDecodeSymbol moduleName typeName =
  "vr_codec_decode_" <> sanitize moduleName <> "_" <> sanitize typeName

sanitize :: String -> String
sanitize = map (\character -> if isAscii character && isAlphaNum character then character else '_')

foreignCIdentifier :: String -> String
foreignCIdentifier = concatMap convert
  where
    convert '\'' = "PRIME"
    convert character
      | isAscii character && (isAlphaNum character || character == '_') = [character]
      | otherwise = "_"

renderType :: LlvmType -> String
renderType typ = case typ of
  I1 -> "i1"
  I8 -> "i8"
  I32 -> "i32"
  I64 -> "i64"
  F64 -> "double"
  Ptr -> "ptr"
  Function {} -> "ptr"
  Record fields -> "{ " <> intercalate ", " (map (renderType . snd) fields) <> " }"

typed :: Operand -> String
typed operand = renderType (operandType operand) <> " " <> operandText operand

emit :: String -> Codegen ()
emit instruction = modify' (\state -> state {codegenInstructions = instruction : codegenInstructions state})

emitInstruction :: String -> Codegen ()
emitInstruction = emit

emitResult :: LlvmType -> String -> Codegen Operand
emitResult typ instruction = do
  register <- gets codegenNextRegister
  modify' (\state -> state {codegenNextRegister = register + 1})
  let name = "%v" <> show register
  emit (name <> " = " <> instruction)
  pure (Operand typ name)

freshLabel :: String -> Codegen String
freshLabel prefix = do
  identifier <- gets codegenNextRegister
  modify' (\state -> state {codegenNextRegister = identifier + 1})
  pure (prefix <> show identifier)

emitBlock :: String -> Codegen ()
emitBlock label = do
  emit (label <> ":")
  modify' (\state -> state {codegenCurrentBlock = label})

allocate :: LlvmType -> Codegen Operand
allocate typ = emitResult Ptr ("call ptr @vr_runtime_alloc_value(i64 " <> sizeOf typ <> ")")

-- LLVM resolves this target-layout constant; emitting two SSA instructions
-- for it at every allocation only adds work for the compiler and optimizer.
sizeOf :: LlvmType -> String
sizeOf typ = "ptrtoint (ptr getelementptr (" <> renderType typ <> ", ptr null, i32 1) to i64)"

allocatePersistent :: LlvmType -> Codegen Operand
allocatePersistent typ = do
  end <- emitResult Ptr ("getelementptr " <> renderType typ <> ", ptr null, i32 1")
  size <- emitResult I64 ("ptrtoint ptr " <> operandText end <> " to i64")
  emitResult Ptr ("call ptr @malloc(i64 " <> operandText size <> ")")

withLocal :: Operand -> Codegen value -> Codegen value
withLocal local action = do
  original <- gets codegenLocals
  modify' (\state -> state {codegenLocals = local : original})
  result <- action
  modify' (\state -> state {codegenLocals = original})
  pure result

ensureOperand :: Located value -> LlvmType -> Operand -> Codegen ()
ensureOperand source expected actual
  | expected == operandType actual = pure ()
  | otherwise = do
      helper <- gets codegenHelperPrefix
      failCodegen source "llvm-operand-type"
        ("In " <> helper <> ": expected " <> show expected <> " (" <> renderType expected
          <> ") but received " <> show (operandType actual) <> " ("
          <> renderType (operandType actual) <> ")")

ensureSame :: M.Expr -> Operand -> Operand -> Codegen ()
ensureSame source left right
  | operandType left == operandType right = pure ()
  | otherwise = failCodegen source "llvm-operand-type" "Intrinsic operands have different LLVM types"

liftEither :: Either Diagnostic value -> Codegen value
liftEither = either (lift . Left) pure

failCodegen :: Located value -> String -> String -> Codegen result
failCodegen source code message = lift (Left (diagnostic BackendPhase code (locatedSpan source) message))

backendFailure :: Located value -> String -> String -> Either Diagnostic result
backendFailure source code message = backendFailureAt (locatedSpan source) code message

backendFailureAt :: Span -> String -> String -> Either Diagnostic result
backendFailureAt at code message = Left (diagnostic BackendPhase code at message)

showInt64 :: Int64 -> String
showInt64 = show

showWord8 :: Word8 -> String
showWord8 = show

-- Preserve first-occurrence numbering while avoiding Data.List.nub's
-- quadratic scan.  String-table indices are externally observable in the
-- emitted module, so sorting the values would not be semantics-preserving.
stableNub :: Ord value => [value] -> [value]
stableNub = reverse . snd . foldl' step (Set.empty, [])
  where
    step accumulated@(seen, values) value
      | Set.member value seen = accumulated
      | otherwise = (Set.insert value seen, value : values)

expressionTag :: M.ExprF -> String
expressionTag expression = case expression of
  M.EPrim {} -> "primitive"; M.ERel {} -> "local"; M.ENamed {} -> "global"
  M.ECon {} -> "constructor"; M.ENone {} -> "none"; M.ESome {} -> "some"
  M.EFfi {} -> "ffi"; M.EFfiApp {} -> "ffi-call"; M.EApp {} -> "application"
  M.EAbs {} -> "lambda"; M.EStaticApp {} -> "static-application"; M.EUnop {} -> "unary"
  M.EBinop {} -> "binary"; M.ERecord {} -> "record"; M.EField {} -> "field"
  M.ERecordConcat {} -> "record-concat"; M.ERecordCut {} -> "record-cut"; M.ECase {} -> "case"
  M.EStrcat {} -> "string-concat"; M.EError {} -> "error"; M.EReturnBlob {} -> "return-blob"
  M.ERedirect {} -> "redirect"; M.EWrite {} -> "write"; M.ESeq {} -> "sequence"
  M.ELet {} -> "let"; M.EClosure {} -> "closure"; M.EQuery {} -> "query"; M.EDml {} -> "dml"
  M.ENextval {} -> "nextval"; M.ESetval {} -> "setval"; M.EUnurlify {} -> "unurlify"
  M.EJavaScript {} -> "javascript"; M.ESignalReturn {} -> "signal-return"
  M.ESignalBind {} -> "signal-bind"; M.ESignalSource {} -> "signal-source"
  M.EServerCall {} -> "server-call"; M.ERecv {} -> "receive"; M.ESleep {} -> "sleep"; M.ESpawn {} -> "spawn"
  M.ESqlCache {} -> "sql-cache"; M.ESqlCacheFlush {} -> "sql-cache-flush"
