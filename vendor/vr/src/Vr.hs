{-# LANGUAGE DerivingStrategies #-}

module Vr
  ( Span (..)
  , ProjectDirective (..)
  , ProjectUnit (..)
  , ProjectPlan (..)
  , ParsedUnit (..)
  , ParsedProject (..)
  , ElaboratedProject (..)
  , ExplicitProject (..)
  , CoreProject (..)
  , MonomorphicProject (..)
  , CompilationOptions (..)
  , SqlCacheHeuristic (..)
  , defaultCompilationOptions
  , parseProject
  , parseSignatureFile
  , checkSignatureFile
  , dumpElaboratedSignatureFile
  , bundledUrWebRoot
  , loadBundledProjectPlan
  , checkStandardLibrary
  , checkBundledStandardLibrary
  , elaborateProject
  , elaborateBundledProject
  , makeExplicitProject
  , makeCoreProject
  , makeMonomorphicProject
  , makeMonomorphicProjectWithOptions
  , compileProjectToMono
  , compileBundledProjectToMono
  , compileBundledProjectToMonoWithOptions
  , compileProjectToLlvm
  , compileBundledProjectToLlvm
  , compileBundledProjectToLlvmWithOptions
  , compileBundledProjectToLlvmBytesWithOptions
  , compileBundledProjectToNativeBuild
  , compileBundledProjectToNativeBuildWithOptions
  , compileBundledProjectToNativeBuildBytesWithOptions
  , bundledNativeLinkInputs
  , bundledNativeIncludeInputs
  , bundledNativeLinker
  , nativeLinkInputsForPlan
  , nativeIncludeInputsForPlan
  , nativeLinkerForPlan
  , compileProjectToJavaScript
  , compileBundledProjectToJavaScript
  , compileProjectToJavaScriptWithRuntime
  , compileBundledProjectToJavaScriptWithRuntime
  , compileBundledProjectToJavaScriptWithRuntimeAndOptions
  , compileBundledProjectToJavaScriptBuild
  , compileBundledProjectToJavaScriptBuildWithOptions
  , checkProject
  , checkBundledProject
  , renderDiagnostic
  ) where

import Control.Exception (IOException, try)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as LazyByteString
import qualified Data.ByteString.Lazy.Char8 as LazyByteString8
import Data.Char (toLower)
import Data.List (find, intercalate, isPrefixOf)
import Paths_vr (getDataFileName)
import Vr.Elaborate (elaborateFileM, elaborateSignature, inferStructure, solveAllConstraints, validateResolvedFile, zonkFile, zonkSignature)
import Vr.Elaborate.Modules (importSignature, selfify, subsignature)
import Vr.Elaborate.State
  ( Environment (..)
  , StructureBinding (..)
  , emptyEnvironment
  , freshGlobal
  , getEnvironment
  , insertStructureBinding
  , putEnvironment
  , runElabM
  )
import Vr.Elaborate.Syntax
  ( Con
  , ConF (..)
  , DeclF (..)
  , File
  , ImportMode (Import)
  , SigItemF (..)
  , Signature
  , SignatureF (..)
  , StructureF (..)
  )
import qualified Vr.Explicit as Explicit
import qualified Vr.Explicit.Syntax as ExplicitSyntax
import qualified Vr.Core.Corify as Corify
import qualified Vr.Core.Reduce as CoreReduce
import qualified Vr.Core.Semantics as CoreSemantics
import qualified Vr.Core.Syntax as CoreSyntax
import qualified Vr.Backend.LLVM as LLVM
import qualified Vr.Backend.JavaScript as JavaScript
import qualified Vr.Backend.NodeAddon as NodeAddon
import qualified Vr.Mono.Analyze as MonoAnalyze
import qualified Vr.Mono.FileCache as MonoFileCache
import qualified Vr.Mono.Fuse as MonoFuse
import qualified Vr.Mono.Lower as Mono
import qualified Vr.Mono.Server as MonoServer
import Vr.Mono.SqlCache (SqlCacheHeuristic (..))
import qualified Vr.Mono.SqlCache as MonoSqlCache
import qualified Vr.Mono.Syntax as MonoSyntax
import qualified Vr.Mono.Validate as MonoValidate
import System.Directory (doesFileExist, getCurrentDirectory)
import System.Environment (getExecutablePath)
import System.FilePath ((</>))
import System.FilePath (normalise, replaceExtension, takeBaseName, takeDirectory, takeExtension)
import qualified Data.Set as Set
import Text.Read (readMaybe)
import Vr.Parse (parseImplementation, parseSignature)
import Vr.Project
import Vr.Source

data ParsedUnit = ParsedUnit
  { parsedUnitProject :: !ProjectUnit
  , parsedUnitSignature :: !(Maybe [SSigItem])
  , parsedUnitImplementation :: !SFile
  }
  deriving stock (Eq, Show)

data ParsedProject = ParsedProject
  { parsedProjectPlan :: !ProjectPlan
  , parsedProjectUnits :: ![ParsedUnit]
  , parsedProjectSource :: !SFile
  }
  deriving stock (Eq, Show)

-- | A complete, solved frontend result.  It includes the pinned Basis and Top
-- declarations so a later backend never needs to reconstruct frontend facts.
data ElaboratedProject = ElaboratedProject
  { elaboratedProjectPlan :: !ProjectPlan
  , elaboratedProjectFile :: !File
  }
  deriving stock (Eq, Show)

-- | Solved program after local recursion and checking-only evidence have been
-- removed, but before modules are evaluated.
data ExplicitProject = ExplicitProject
  { explicitProjectPlan :: !ProjectPlan
  , explicitProjectFile :: !ExplicitSyntax.File
  }
  deriving stock (Eq, Show)

-- | Whole program after structures, signatures, functors, and projections
-- have been flattened into the polymorphic Core language.
data CoreProject = CoreProject
  { coreProjectPlan :: !ProjectPlan
  , coreProjectFile :: !CoreSyntax.File
  }
  deriving stock (Eq, Show)

-- | Backend handoff: a module-free program with concrete runtime types and
-- resolved static operands, but no JavaScript, C, LLVM, or SQL backend policy.
data MonomorphicProject = MonomorphicProject
  { monomorphicProjectPlan :: !ProjectPlan
  , monomorphicProjectFile :: !MonoSyntax.File
  }
  deriving stock (Eq, Show)

parseProject :: FilePath -> IO (Either [Diagnostic] ParsedProject)
parseProject = parseProjectWithLibrary Nothing

parseProjectWithLibrary :: Maybe FilePath -> FilePath -> IO (Either [Diagnostic] ParsedProject)
parseProjectWithLibrary standardLibrary target = do
  loaded <- loadProjectWithLibrary standardLibrary target
  case loaded of
    Left problems -> pure (Left problems)
    Right plan -> do
      case reservedStandardUnit standardLibrary plan of
        Just unit ->
          pure (Left [diagnostic ProjectPhase "duplicate-standard-module" (fileSpan (projectUnitImplementation unit)) ("Duplicate top-level module name " <> last (projectUnitModule unit))])
        Nothing -> do
          parsed <- mapM parseUnit (projectUnits plan)
          ffiParsed <- mapM parseFfiDirective
            [directive | directive <- projectDirectives plan, projectDirectiveName directive == "ffi"]
          let problems = concat [unitProblems | Left unitProblems <- parsed]
                <> concat [ffiProblems | Left ffiProblems <- ffiParsed]
          if not (null problems)
            then pure (Left problems)
            else do
              let units = [unit | Right unit <- parsed]
                  ffiDeclarations = [declaration | Right declaration <- ffiParsed]
                  source = syntheticPrefix plan <> ffiDeclarations <> map unitDeclaration units <> syntheticSuffix plan
              pure
                ( Right
                    ParsedProject
                      { parsedProjectPlan = plan
                      , parsedProjectUnits = units
                      , parsedProjectSource = source
                      }
                )

reservedStandardUnit :: Maybe FilePath -> ProjectPlan -> Maybe ProjectUnit
reservedStandardUnit Nothing _ = Nothing
reservedStandardUnit (Just _) plan = find reserved (projectUnits plan)
  where
    reserved unit = case reverse (projectUnitModule unit) of
      name : _ -> name `elem` ["Basis", "Top"]
      [] -> False

parseFfiDirective :: ProjectDirective -> IO (Either [Diagnostic] SDecl)
parseFfiDirective directive = do
  let raw = projectDirectiveArgument directive
      base0 = if takeExtension raw `elem` [".ur", ".urs"] then initExtension raw else raw
      base = normalise (takeDirectory (spanFile (projectDirectiveSpan directive)) </> base0)
      signatureFile = base <> ".urs"
      at = projectDirectiveSpan directive
      name = moduleNameOf (takeBaseName base)
  exists <- doesFileExist signatureFile
  if not exists
    then pure (Left [diagnostic ProjectPhase "missing-ffi-signature" at ("Missing FFI signature " <> signatureFile)])
    else do
      parsed <- parseSignature signatureFile <$> BS.readFile signatureFile
      pure (fmap (\items -> Located at (SDFfiStr name (Located at (SSigConst items)) Nothing)) parsed)
  where
    initExtension path = reverse (drop 1 (dropWhile (/= '.') (reverse path)))

parseSignatureFile :: FilePath -> IO (Either [Diagnostic] [SSigItem])
parseSignatureFile target = parseSignature target <$> BS.readFile target

checkSignatureFile :: FilePath -> IO (Either [Diagnostic] ())
checkSignatureFile target = fmap (fmap (const ())) (dumpElaboratedSignatureFile target)

dumpElaboratedSignatureFile :: FilePath -> IO (Either [Diagnostic] Signature)
dumpElaboratedSignatureFile target = do
  parsed <- parseSignatureFile target
  pure $ parsed >>= \items ->
    let at = fileSpan target
        (result, _) = runElabM emptyEnvironment $ do
          (signature, _) <- elaborateSignature emptyEnvironment (Located at (SSigConst items))
          solveAllConstraints
          zonkSignature signature
     in result

checkStandardLibrary :: FilePath -> IO (Either [Diagnostic] ())
checkStandardLibrary root = do
  let library = root </> "lib" </> "ur"
      basisFile = library </> "basis.urs"
      topSignatureFile = library </> "top.urs"
      topImplementationFile = library </> "top.ur"
  basisParsed <- parseSignatureFile basisFile
  topSignatureParsed <- parseSignatureFile topSignatureFile
  topImplementationParsed <- parseImplementation topImplementationFile <$> BS.readFile topImplementationFile
  pure $ do
    basisItems <- basisParsed
    topItems <- topSignatureParsed
    topDeclarations <- topImplementationParsed
    let (result, _) = runElabM emptyEnvironment $ do
          (basisSignature, _) <- elaborateSignature emptyEnvironment (Located (fileSpan basisFile) (SSigConst basisItems))
          solveAllConstraints
          basisIdentifier <- freshGlobal
          current <- getEnvironment
          let publicBasis = selfify basisIdentifier [] basisSignature
              withBasisStructure = insertStructureBinding "Basis" (StructureBinding basisIdentifier publicBasis) current
              withBasis = importSignature Import publicBasis withBasisStructure
          putEnvironment withBasis
          (topSignature, _) <- elaborateSignature withBasis (Located (fileSpan topSignatureFile) (SSigConst topItems))
          solveAllConstraints
          (topStructure, actualTopSignature) <- inferStructure withBasis (Located (fileSpan topImplementationFile) (SStrConst topDeclarations))
          subsignature withBasis (fileSpan topImplementationFile) actualTopSignature topSignature
          solveAllConstraints
          topIdentifier <- freshGlobal
          let publicTop = selfify topIdentifier [] topSignature
              withTopStructure =
                (insertStructureBinding "Top" (StructureBinding topIdentifier publicTop) withBasis)
                  {environmentTopId = Just topIdentifier}
              _withTop = importSignature Import publicTop withTopStructure
              _checkedStructure = topStructure
          pure ()
     in result

-- | Locate the Ur/Web compatibility corpus installed with Vr.
bundledUrWebRoot :: IO FilePath
bundledUrWebRoot = do
  installed <- getDataFileName ("vendor" </> "urweb")
  workingDirectory <- getCurrentDirectory
  executable <- getExecutablePath
  firstCorpus
    ( installed
        : map (</> "vendor" </> "urweb")
          (directoryAncestors workingDirectory <> directoryAncestors (takeDirectory executable))
    )
  where
    firstCorpus [] = getDataFileName ("vendor" </> "urweb")
    firstCorpus (candidate : rest) = do
      exists <- doesFileExist (candidate </> "lib" </> "ur" </> "basis.urs")
      if exists then pure candidate else firstCorpus rest
    directoryAncestors directory =
      directory : let parent = takeDirectory directory
                   in if parent == directory then [] else directoryAncestors parent

-- | Load only the ordered project plan against Vr's vendored standard
-- library.  Build frontends use this after code generation for output
-- directives such as @sql@ without repeating parsing and elaboration.
loadBundledProjectPlan :: FilePath -> IO (Either [Diagnostic] ProjectPlan)
loadBundledProjectPlan target = do
  root <- bundledUrWebRoot
  loadProjectWithLibrary (Just (root </> "lib" </> "ur")) target

-- | Check the vendored Basis and Top sources.
checkBundledStandardLibrary :: IO (Either [Diagnostic] ())
checkBundledStandardLibrary = bundledUrWebRoot >>= checkStandardLibrary

-- | Elaborate a complete project against the pinned source standard library.
-- The standard environment is rebuilt through the same frontend judgments as
-- ordinary source, and the returned file is fully zonked for a later backend.
elaborateProject :: FilePath -> FilePath -> IO (Either [Diagnostic] ElaboratedProject)
elaborateProject root target = do
  let library = root </> "lib" </> "ur"
      basisFile = library </> "basis.urs"
      topSignatureFile = library </> "top.urs"
      topImplementationFile = library </> "top.ur"
  parsedProject <- parseProjectWithLibrary (Just library) target
  basisParsed <- parseSignatureFile basisFile
  topSignatureParsed <- parseSignatureFile topSignatureFile
  topImplementationParsed <- parseImplementation topImplementationFile <$> BS.readFile topImplementationFile
  pure $ do
    project <- parsedProject
    basisItems <- basisParsed
    topItems <- topSignatureParsed
    topDeclarations <- topImplementationParsed
    let (result, _) = runElabM emptyEnvironment $ do
          (basisSignature, _) <- elaborateSignature emptyEnvironment (Located (fileSpan basisFile) (SSigConst basisItems))
          solveAllConstraints
          basisIdentifier <- freshGlobal
          current <- getEnvironment
          let publicBasis = selfify basisIdentifier [] basisSignature
              withBasisStructure = insertStructureBinding "Basis" (StructureBinding basisIdentifier publicBasis) current
              withBasis = importSignature Import publicBasis withBasisStructure
          putEnvironment withBasis
          (topSignature, _) <- elaborateSignature withBasis (Located (fileSpan topSignatureFile) (SSigConst topItems))
          solveAllConstraints
          (topStructure, actualTopSignature) <- inferStructure withBasis (Located (fileSpan topImplementationFile) (SStrConst topDeclarations))
          subsignature withBasis (fileSpan topImplementationFile) actualTopSignature topSignature
          solveAllConstraints
          topIdentifier <- freshGlobal
          let publicTop = selfify topIdentifier [] topSignature
              withTopStructure =
                (insertStructureBinding "Top" (StructureBinding topIdentifier publicTop) withBasis)
                  {environmentTopId = Just topIdentifier}
              withStandard =
                (importSignature Import publicTop withTopStructure)
                  { environmentLessSafeFfi = any ((== "lessSafeFfi") . projectDirectiveName) (projectDirectives (parsedProjectPlan project))
                  }
          putEnvironment withStandard
          file <- elaborateFileM (parsedProjectSource project)
          solveAllConstraints
          -- The declaration carries the FFI's defining signature.  The
          -- selfified signature belongs only in the environment seen by
          -- clients; storing it here turns each Basis datatype into an import
          -- from Basis itself and makes module flattening circular.
          let basisDeclaration = Located (fileSpan basisFile) (DFfiStr "Basis" basisIdentifier basisSignature)
              topDeclaration = Located (fileSpan topImplementationFile) (DStr "Top" topIdentifier publicTop topStructure)
              completeFile = basisDeclaration : topDeclaration : file
          validateResolvedFile completeFile
          solvedFile <- zonkFile completeFile
          let plan = addInlineFfiDirectives (parsedProjectPlan project) solvedFile
          pure
            ElaboratedProject
              { elaboratedProjectPlan = plan
              , elaboratedProjectFile = solvedFile
              }
     in result

-- | Elaborate a project against Vr's vendored Ur/Web compatibility profile.
elaborateBundledProject :: FilePath -> IO (Either [Diagnostic] ElaboratedProject)
elaborateBundledProject target = do
  root <- bundledUrWebRoot
  elaborateProject root target

makeExplicitProject :: ElaboratedProject -> Either [Diagnostic] ExplicitProject
makeExplicitProject project = do
  file <- Explicit.explicitFile (elaboratedProjectFile project)
  pure ExplicitProject
    { explicitProjectPlan = elaboratedProjectPlan project
    , explicitProjectFile = file
    }

makeCoreProject :: ExplicitProject -> Either [Diagnostic] CoreProject
makeCoreProject project = do
  file <- Corify.corifyFileWithRewrites
    (projectRewriteRules (explicitProjectPlan project))
    (explicitProjectFile project)
  pure CoreProject
    { coreProjectPlan = explicitProjectPlan project
    , coreProjectFile = file
    }

makeMonomorphicProject :: CoreProject -> Either [Diagnostic] MonomorphicProject
makeMonomorphicProject = makeMonomorphicProjectWithOptions defaultCompilationOptions

-- | Whole-compiler switches that are not part of an Ur/Web project file.
-- SQL caching is a command-line compiler extension in the reference driver,
-- so keeping it here avoids incorrectly accepting @sqlcache@ as a @.urp@
-- directive.
data CompilationOptions = CompilationOptions
  { compilationSqlCache :: !Bool
  , compilationSqlCacheHeuristic :: !SqlCacheHeuristic
  }
  deriving stock (Eq, Ord, Show)

defaultCompilationOptions :: CompilationOptions
defaultCompilationOptions = CompilationOptions
  { compilationSqlCache = False
  , compilationSqlCacheHeuristic = MonoSqlCache.NoPureOne
  }

makeMonomorphicProjectWithOptions
  :: CompilationOptions
  -> CoreProject
  -> Either [Diagnostic] MonomorphicProject
makeMonomorphicProjectWithOptions options project = do
  case projectFileCache plan of
    Just directive
      | map toLower (projectDatabaseSystem plan) `notElem` ["postgres", "mysql"] ->
          Left [diagnostic MonoPhase "file-cache-database"
            (projectDirectiveSpan directive)
            "The selected database engine is incompatible with file caching"]
    _ -> pure ()
  lowered <- Mono.monoizeFileWithProjectSettings
    (coreReduceSettings plan)
    (coreSemanticSettings plan)
    (projectUrlPrefix plan)
    (projectDatabaseSystem plan)
    (projectMangleSql plan)
    (coreProjectFile project)
  validated <- MonoValidate.validateFile (case projectFileCache plan of
    Nothing -> lowered
    Just _ -> MonoFileCache.instrumentFile (projectDatabaseSystem plan) lowered)
  analyzed <- MonoAnalyze.analyzeFileWithFilters
    (projectFilterRules plan)
    validated
  let fused = MonoFuse.fuseFile analyzed
      cacheInput = MonoFuse.fuseFile (MonoFuse.inlineFullFile fused)
  file <- MonoValidate.validateFile
    (if compilationSqlCache options
      then MonoSqlCache.instrumentFile (compilationSqlCacheHeuristic options) cacheInput
      else fused)
  pure MonomorphicProject
    { monomorphicProjectPlan = plan
    , monomorphicProjectFile = file
    }
  where
    plan = coreProjectPlan project

projectFileCache :: ProjectPlan -> Maybe ProjectDirective
projectFileCache = find ((== "filecache") . projectDirectiveName) . projectDirectives

projectDatabaseSystem :: ProjectPlan -> String
projectDatabaseSystem plan = case
  [ projectDirectiveArgument directive
  | directive <- projectDirectives plan
  , projectDirectiveName directive == "dbms"
  ] of
  selected : _ -> selected
  [] -> "postgres"

projectMangleSql :: ProjectPlan -> Bool
projectMangleSql plan = not (any ((== "noMangleSql") . projectDirectiveName)
  (projectDirectives plan))

coreReduceSettings :: ProjectPlan -> CoreReduce.ReduceSettings
coreReduceSettings plan =
  CoreReduce.ReduceSettings
    { CoreReduce.reduceCoreInline = maybe 5 id (lastInteger "coreInline")
    , CoreReduce.reduceNeverInline = arguments "neverInline"
    }
  where
    matching name = filter ((== name) . projectDirectiveName) (projectDirectives plan)
    arguments name = Set.fromList (map projectDirectiveArgument (matching name))
    lastInteger name = case reverse (matching name) of
      directive : _ -> readMaybe (projectDirectiveArgument directive)
      [] -> Nothing

coreSemanticSettings :: ProjectPlan -> CoreSemantics.SemanticSettings
coreSemanticSettings plan = defaults
  { CoreSemantics.semanticClientToServer =
      CoreSemantics.semanticClientToServer defaults <> foreignNames "clientToServer"
  , CoreSemantics.semanticEffectful =
      CoreSemantics.semanticEffectful defaults
        <> foreignNames "effectful"
        <> Set.difference (foreignNames "ffiTransaction") benign
  , CoreSemantics.semanticBenignEffectful = benign
  , CoreSemantics.semanticClientOnly =
      CoreSemantics.semanticClientOnly defaults <> foreignNames "clientOnly"
  , CoreSemantics.semanticServerOnly =
      CoreSemantics.semanticServerOnly defaults <> foreignNames "serverOnly"
  , CoreSemantics.semanticSafeGetDefault =
      CoreSemantics.semanticSafeGetDefault defaults || not (null (arguments "safeGetDefault"))
  , CoreSemantics.semanticSafeGets = Set.fromList (arguments "safeGet")
  }
  where
    defaults = CoreSemantics.defaultSemanticSettings
    benign = CoreSemantics.semanticBenignEffectful defaults <> foreignNames "benignEffectful"
    arguments name =
      [ projectDirectiveArgument directive
      | directive <- projectDirectives plan
      , projectDirectiveName directive == name
      ]
    foreignNames name = Set.fromList
      [ (moduleName, drop 1 member)
      | value <- arguments name
      , let (moduleName, member) = break (== '.') value
      , not (null moduleName)
      , not (null member)
      ]

projectUrlPrefix :: ProjectPlan -> String
projectUrlPrefix plan = case
  [ projectDirectiveArgument directive
  | directive <- projectDirectives plan
  , projectDirectiveName directive == "prefix"
  ] of
  [] -> "/"
  values -> normalizePrefix (last values)
  where
    normalizePrefix "" = "/"
    normalizePrefix value0
      | "http://" `isPrefixOf` value0 = normalizePrefix (originPath (drop 7 value0))
      | "https://" `isPrefixOf` value0 = normalizePrefix (originPath (drop 8 value0))
      where
        originPath value = case dropWhile (/= '/') value of
          "" -> "/"
          path -> path
    normalizePrefix value
      | last value == '/' = value
      | otherwise = value <> "/"

compileProjectToMono :: FilePath -> FilePath -> IO (Either [Diagnostic] MonomorphicProject)
compileProjectToMono root target = do
  elaborated <- elaborateProject root target
  pure (elaborated >>= makeExplicitProject >>= makeCoreProject >>= makeMonomorphicProject)

compileBundledProjectToMono :: FilePath -> IO (Either [Diagnostic] MonomorphicProject)
compileBundledProjectToMono = compileBundledProjectToMonoWithOptions defaultCompilationOptions

compileBundledProjectToMonoWithOptions
  :: CompilationOptions
  -> FilePath
  -> IO (Either [Diagnostic] MonomorphicProject)
compileBundledProjectToMonoWithOptions options target = do
  root <- bundledUrWebRoot
  elaborated <- elaborateProject root target
  pure (elaborated >>= makeExplicitProject >>= makeCoreProject
    >>= makeMonomorphicProjectWithOptions options)

-- | Run the complete frontend and middle end, then emit one textual LLVM
-- module using the native backend's C-compatible process entry point.
compileProjectToLlvm :: FilePath -> FilePath -> IO (Either [Diagnostic] String)
compileProjectToLlvm root target = do
  mono <- compileProjectToMono root target
  case mono of
    Left problems -> pure (Left problems)
    Right project -> do
      assets <- loadStaticAssets (monomorphicProjectPlan project)
      scripts <- loadJavaScriptFiles (monomorphicProjectPlan project)
      pure $ do
        loadedAssets <- assets
        loadedScripts <- scripts
        LLVM.emitLlvmProjectWithAssetsAndScripts
          (monomorphicProjectPlan project)
          loadedAssets
          loadedScripts
          (monomorphicProjectFile project)

-- | Compile against Vr's vendored Ur/Web Basis and Top definitions.
compileBundledProjectToLlvm :: FilePath -> IO (Either [Diagnostic] String)
compileBundledProjectToLlvm = compileBundledProjectToLlvmWithOptions defaultCompilationOptions

compileBundledProjectToLlvmWithOptions
  :: CompilationOptions
  -> FilePath
  -> IO (Either [Diagnostic] String)
compileBundledProjectToLlvmWithOptions options target =
  fmap (fmap LazyByteString8.unpack)
    (compileBundledProjectToLlvmBytesWithOptions options target)

-- | Byte-oriented counterpart used by the CLI and native build cache.  This
-- keeps large textual modules out of the linked-list String representation.
compileBundledProjectToLlvmBytesWithOptions
  :: CompilationOptions
  -> FilePath
  -> IO (Either [Diagnostic] LazyByteString.ByteString)
compileBundledProjectToLlvmBytesWithOptions options target = do
  mono <- compileBundledProjectToMonoWithOptions options target
  case mono of
    Left problems -> pure (Left problems)
    Right project -> do
      assets <- loadStaticAssets (monomorphicProjectPlan project)
      scripts <- loadJavaScriptFiles (monomorphicProjectPlan project)
      pure $ do
        loadedAssets <- assets
        loadedScripts <- scripts
        LLVM.emitLlvmProjectWithAssetsAndScriptsBytes
          (monomorphicProjectPlan project)
          loadedAssets loadedScripts (monomorphicProjectFile project)

-- | Compile a native executable's LLVM module together with the generated C
-- ABI adapters needed for representation-independent abstract FFI values.
compileBundledProjectToNativeBuild
  :: FilePath
  -> IO (Either [Diagnostic] (String, String))
compileBundledProjectToNativeBuild =
  compileBundledProjectToNativeBuildWithOptions defaultCompilationOptions

compileBundledProjectToNativeBuildWithOptions
  :: CompilationOptions
  -> FilePath
  -> IO (Either [Diagnostic] (String, String))
compileBundledProjectToNativeBuildWithOptions options target =
  fmap (fmap (\(llvm, shim) -> (LazyByteString8.unpack llvm, shim)))
    (compileBundledProjectToNativeBuildBytesWithOptions options target)

-- | Native build input with compact LLVM bytes.  The compatibility function
-- above retains the original String result for library users.
compileBundledProjectToNativeBuildBytesWithOptions
  :: CompilationOptions
  -> FilePath
  -> IO (Either [Diagnostic] (LazyByteString.ByteString, String))
compileBundledProjectToNativeBuildBytesWithOptions options target = do
  mono <- compileBundledProjectToMonoWithOptions options target
  case mono of
    Left problems -> pure (Left problems)
    Right project -> do
      let plan = monomorphicProjectPlan project
          file = monomorphicProjectFile project
          codecs = NodeAddon.collectForeignCodecs plan
          constructors = MonoServer.serverForeignConstructors plan file
      assets <- loadStaticAssets plan
      scripts <- loadJavaScriptFiles plan
      case NodeAddon.collectNativeShimBindings plan file of
        Left problems -> pure (Left problems)
        Right bindings -> do
          -- A project header may define a directly called C function even
          -- when no abstract-value ABI adapter is required. Preserve include
          -- directives independently of whether we generated adapter bindings.
          includes <- nativeIncludeInputsForPlan plan
          pure $ do
            loadedAssets <- assets
            loadedScripts <- scripts
            resolvedIncludes <- includes
            llvm <- case LLVM.emitLlvmProjectWithAssetsAndScriptsBytes
              plan loadedAssets loadedScripts file of
                Left problems -> Left problems
                Right output -> Right output
            Right (llvm, NodeAddon.renderNativeShim resolvedIncludes bindings codecs constructors)

-- | Resolve native @link@ inputs using the same recursively loaded project
-- plan as compilation.  When a requested object is absent but a sibling C
-- source exists, the CLI passes that source to Clang directly; this keeps the
-- vendored Ur/Web FFI examples runnable without committing host-specific
-- object files.
bundledNativeLinkInputs :: FilePath -> IO (Either [Diagnostic] [FilePath])
bundledNativeLinkInputs target = do
  loaded <- loadBundledProjectPlan target
  case loaded of
    Left problems -> pure (Left problems)
    Right plan -> nativeLinkInputsForPlan plan

-- | Resolve native link inputs from an already loaded project plan.  Build
-- drivers use this form to avoid parsing the complete Ur module graph again
-- after code generation.
nativeLinkInputsForPlan :: ProjectPlan -> IO (Either [Diagnostic] [FilePath])
nativeLinkInputsForPlan = resolveProjectInputs True "link"

-- | Resolve C headers named by @include@ using the same per-directive source
-- directory rules as native @link@ inputs.
bundledNativeIncludeInputs :: FilePath -> IO (Either [Diagnostic] [FilePath])
bundledNativeIncludeInputs target = do
  root <- bundledUrWebRoot
  parsed <- parseProjectWithLibrary (Just (root </> "lib" </> "ur")) target
  case parsed of
    Left problems -> pure (Left problems)
    Right project -> nativeIncludeInputsForPlan (parsedProjectPlan project)

-- | Resolve include directives after a caller has already compiled or validated
-- its project. Header resolution depends only on the ordered project plan,
-- not on parsing the Ur implementations again.
nativeIncludeInputsForPlan :: ProjectPlan -> IO (Either [Diagnostic] [FilePath])
nativeIncludeInputsForPlan = resolveProjectInputs False "include"

resolveProjectInputs :: Bool -> String -> ProjectPlan -> IO (Either [Diagnostic] [FilePath])
resolveProjectInputs linkFallback directiveName plan = do
  resolved <- mapM (resolveProjectInput linkFallback)
    [ directive
    | directive <- projectDirectives plan
    , projectDirectiveName directive == directiveName
    ]
  let problems = [problem | Left problem <- resolved]
  pure (if null problems then Right [input | Right input <- resolved] else Left problems)

resolveProjectInput :: Bool -> ProjectDirective -> IO (Either Diagnostic FilePath)
resolveProjectInput linkFallback directive
  | linkFallback && "-" `isPrefixOf` argument = pure (Right argument)
  | otherwise = do
      let requested = normalise
            (takeDirectory (spanFile (projectDirectiveSpan directive)) </> argument)
          source = replaceExtension requested "c"
      requestedExists <- doesFileExist requested
      sourceExists <- if linkFallback then doesFileExist source else pure False
      pure $ if requestedExists
        then Right requested
        else if sourceExists
          then Right source
          else Left (diagnostic BackendPhase code
            (projectDirectiveSpan directive)
            (label <> requested))
  where
    argument = projectDirectiveArgument directive
    code = if linkFallback then "native-link" else "native-include"
    label = if linkFallback
      then "Native link input does not exist: "
      else "Native include input does not exist: "

-- | Return the last custom linker command selected by the recursively loaded
-- project, matching the reference driver's command override semantics.
bundledNativeLinker :: FilePath -> IO (Either [Diagnostic] (Maybe String))
bundledNativeLinker target = do
  loaded <- loadBundledProjectPlan target
  pure $ do
    plan <- loaded
    pure (nativeLinkerForPlan plan)

-- | Select the last custom linker directive from an already loaded plan.
nativeLinkerForPlan :: ProjectPlan -> Maybe String
nativeLinkerForPlan plan = case reverse
  [ projectDirectiveArgument directive
  | directive <- projectDirectives plan
  , projectDirectiveName directive == "linker"
  ] of
    command : _ -> Just command
    [] -> Nothing

-- | Compile a project to an ordinary ECMAScript module that imports Vr's
-- runtime from @./vr_runtime.mjs@.
compileProjectToJavaScript :: FilePath -> FilePath -> IO (Either [Diagnostic] String)
compileProjectToJavaScript root target =
  compileProjectToJavaScriptWithRuntime root target "./vr_runtime.mjs"

-- | Compile against the vendored standard library to direct JavaScript.
compileBundledProjectToJavaScript :: FilePath -> IO (Either [Diagnostic] String)
compileBundledProjectToJavaScript target =
  compileBundledProjectToJavaScriptWithRuntime target "./vr_runtime.mjs"

-- | Compile to direct JavaScript with an explicit runtime module specifier.
-- The CLI uses this variant when placing a runtime next to an output file.
compileProjectToJavaScriptWithRuntime
  :: FilePath
  -> FilePath
  -> String
  -> IO (Either [Diagnostic] String)
compileProjectToJavaScriptWithRuntime root target runtimeImport = do
  mono <- compileProjectToMono root target
  case mono of
    Left problems -> pure (Left problems)
    Right project -> do
      assets <- loadStaticAssets (monomorphicProjectPlan project)
      scripts <- loadJavaScriptFiles (monomorphicProjectPlan project)
      pure $ do
        loadedAssets <- assets
        loadedScripts <- scripts
        JavaScript.emitJavaScriptProject
          runtimeImport
          (monomorphicProjectPlan project)
          loadedAssets
          loadedScripts
          (monomorphicProjectFile project)

-- | Compile against the vendored standard library with an explicit runtime
-- import used by the generated module.
compileBundledProjectToJavaScriptWithRuntime
  :: FilePath
  -> String
  -> IO (Either [Diagnostic] String)
compileBundledProjectToJavaScriptWithRuntime =
  compileBundledProjectToJavaScriptWithRuntimeAndOptions defaultCompilationOptions

compileBundledProjectToJavaScriptWithRuntimeAndOptions
  :: CompilationOptions
  -> FilePath
  -> String
  -> IO (Either [Diagnostic] String)
compileBundledProjectToJavaScriptWithRuntimeAndOptions options target runtimeImport = do
  mono <- compileBundledProjectToMonoWithOptions options target
  case mono of
    Left problems -> pure (Left problems)
    Right project -> do
      assets <- loadStaticAssets (monomorphicProjectPlan project)
      scripts <- loadJavaScriptFiles (monomorphicProjectPlan project)
      pure $ do
        loadedAssets <- assets
        loadedScripts <- scripts
        JavaScript.emitJavaScriptProject runtimeImport
          (monomorphicProjectPlan project) loadedAssets loadedScripts
          (monomorphicProjectFile project)

-- | Compile a direct-JavaScript application together with the generated C
-- half of its optional Node N-API sidecar.  The caller chooses the relative
-- addon module path written into JavaScript and is responsible for invoking a
-- C compiler when the returned source is present.
compileBundledProjectToJavaScriptBuild
  :: FilePath
  -> String
  -> String
  -> IO (Either [Diagnostic] (String, Maybe String))
compileBundledProjectToJavaScriptBuild =
  compileBundledProjectToJavaScriptBuildWithOptions defaultCompilationOptions

compileBundledProjectToJavaScriptBuildWithOptions
  :: CompilationOptions
  -> FilePath
  -> String
  -> String
  -> IO (Either [Diagnostic] (String, Maybe String))
compileBundledProjectToJavaScriptBuildWithOptions options target runtimeImport addonImport = do
  mono <- compileBundledProjectToMonoWithOptions options target
  case mono of
    Left problems -> pure (Left problems)
    Right project -> do
      let plan = monomorphicProjectPlan project
          file = monomorphicProjectFile project
          codecs = NodeAddon.collectForeignCodecs plan
          constructors = MonoServer.serverForeignConstructors plan file
      assets <- loadStaticAssets plan
      scripts <- loadJavaScriptFiles plan
      case NodeAddon.collectForeignBindings plan file of
        Left problems -> pure (Left problems)
        Right bindings -> do
          includes <- if null bindings && null codecs && null constructors
            then pure (Right [])
            else resolveProjectInputs False "include" plan
          pure $ do
            loadedAssets <- assets
            loadedScripts <- scripts
            resolvedIncludes <- includes
            javascript <- JavaScript.emitJavaScriptProjectWithForeignAddon
              runtimeImport addonImport plan loadedAssets loadedScripts file
            let addon = Just (NodeAddon.renderNodeAddon resolvedIncludes bindings codecs constructors)
            Right (javascript, addon)

loadStaticAssets :: ProjectPlan -> IO (Either [Diagnostic] [ProjectAsset])
loadStaticAssets plan = do
  customMimeTypes <- loadMimeTypes
  case customMimeTypes of
    Left problem -> pure (Left [problem])
    Right mimeTypes -> do
      loaded <- mapM (load mimeTypes) directives
      let problems = [problem | Left problem <- loaded]
      pure $ if null problems then Right [asset | Right asset <- loaded] else Left problems
  where
    directives = filter ((== "file") . projectDirectiveName) (projectDirectives plan)
    mimeDirectives = filter ((== "mimeTypes") . projectDirectiveName) (projectDirectives plan)
    load mimeTypes directive = case words (projectDirectiveArgument directive) of
      [uri, file] -> readAsset directive uri file (guessMime mimeTypes file)
      [uri, file, mime] -> readAsset directive uri file mime
      _ -> pure (Left (diagnostic BackendPhase "llvm-static-file" (projectDirectiveSpan directive) "Malformed static file directive"))
    readAsset directive uri file mime = do
      let source = normalise (takeDirectory (spanFile (projectDirectiveSpan directive)) </> file)
          normalizedUri = case uri of
            '/' : _ -> uri
            _ -> '/' : uri
      bytes <- try (BS.readFile source) :: IO (Either IOException BS.ByteString)
      pure $ case bytes of
        Left problem -> Left (diagnostic BackendPhase "llvm-static-file" (projectDirectiveSpan directive)
          ("Unable to read static asset " <> source <> ": " <> show problem))
        Right contents -> Right ProjectAsset
          { projectAssetUri = B8.pack normalizedUri
          , projectAssetMime = B8.pack mime
          , projectAssetBytes = contents
          }
    loadMimeTypes = case reverse mimeDirectives of
      [] -> pure (Right Nothing)
      directive : _ -> do
        let source = normalise
              (takeDirectory (spanFile (projectDirectiveSpan directive))
                </> projectDirectiveArgument directive)
        contents <- try (BS.readFile source) :: IO (Either IOException BS.ByteString)
        pure $ case contents of
          Left problem -> Left (diagnostic BackendPhase "mime-types" (projectDirectiveSpan directive)
            ("Unable to read MIME types file " <> source <> ": " <> show problem))
          Right bytes -> Right (Just
            [ (B8.unpack extension, B8.unpack mime)
            | line <- B8.lines bytes
            , let fields = B8.words line
            , mime : extensions <- [fields]
            , extension <- extensions
            ])
    guessMime (Just mimeTypes) file = case lookup (dropWhile (== '.') (takeExtension file)) mimeTypes of
      Just mime -> mime
      Nothing -> "application/octet-stream"
    guessMime Nothing file = case takeExtension file of
      ".css" -> "text/css; charset=utf-8"
      ".html" -> "text/html; charset=utf-8"
      ".js" -> "text/javascript; charset=utf-8"
      ".json" -> "application/json"
      ".png" -> "image/png"
      ".svg" -> "image/svg+xml"
      ".txt" -> "text/plain; charset=utf-8"
      _ -> "application/octet-stream"

-- Project-level FFI modes and modes written on direct @ffi@ declarations have
-- identical downstream meaning in Ur/Web.  Keep one ordered directive stream
-- after elaboration so Core semantics and both backends see both spellings.
addInlineFfiDirectives :: ProjectPlan -> File -> ProjectPlan
addInlineFfiDirectives plan file = plan
  { projectDirectives = projectDirectives plan <> concatMap (declaration []) file
  }
  where
    transactionConstructorIds = Set.fromList
      [ identifier
      | source <- file
      , DFfiStr "Basis" _ signature <- [locatedValue source]
      , identifier <- signatureConstructorIds "transaction" signature
      ]
    signatureConstructorIds name signature = case locatedValue signature of
      SgnConst items ->
        [identifier | item <- items, SgiConAbs found identifier _ <- [locatedValue item], found == name]
          <> [identifier | item <- items, SgiCon found identifier _ _ <- [locatedValue item], found == name]
      SgnWhere base _ _ _ -> signatureConstructorIds name base
      _ -> []
    declaration modules source = case locatedValue source of
      DFfi name _ modes typ ->
        let qualified = foreignName modules name
            configured = map (modeDirective source qualified) modes
            defaultMapping =
              [ProjectDirective "jsFunc" (qualified <> "=" <> name) (locatedSpan source)
              | not (any isJavaScriptMode modes)]
         in configured <> defaultMapping <> typeDirectives source qualified typ
      DFfiStr moduleName _ signature
        | moduleName /= "Basis" -> signatureDirectives source moduleName signature
      DStr name _ _ structure -> structureDirectives (modules <> [name]) structure
      _ -> []
    structureDirectives modules source = case locatedValue source of
      StrConst declarations -> concatMap (declaration modules) declarations
      StrFun _ _ _ _ body -> structureDirectives modules body
      StrApp function argument ->
        structureDirectives modules function <> structureDirectives modules argument
      StrProj parent _ -> structureDirectives modules parent
      StrVar _ -> []
      StrError -> []
    -- Core foreign identities use the innermost structure name, matching the
    -- reference compiler's handling of direct FFI declarations.
    foreignName modules name = case reverse modules of
      moduleName : _ -> intercalate "." [moduleName, name]
      [] -> name
    isJavaScriptMode mode = case mode of
      FfiJsFunc _ -> True
      _ -> False
    modeDirective source qualified mode = ProjectDirective directiveName argument (locatedSpan source)
      where
        (directiveName, argument) = case mode of
          FfiEffectful -> ("effectful", qualified)
          FfiBenignEffectful -> ("benignEffectful", qualified)
          FfiClientOnly -> ("clientOnly", qualified)
          FfiServerOnly -> ("serverOnly", qualified)
          FfiJsFunc javascriptName -> ("jsFunc", qualified <> "=" <> javascriptName)
    signatureDirectives source moduleName signature = case locatedValue signature of
      SgnConst items -> concatMap (signatureItem source moduleName) items
      SgnWhere base _ _ _ -> signatureDirectives source moduleName base
      _ -> []
    signatureItem source moduleName item = case locatedValue item of
      SgiVal name _ typ -> typeDirectives source (moduleName <> "." <> name) typ
      _ -> []
    typeDirectives source qualified typ =
      ProjectDirective "ffiArity" (qualified <> "=" <> show (valueArity typ)) (locatedSpan source)
        : [ProjectDirective "ffiTransaction" qualified (locatedSpan source) | returnsTransaction typ]
    valueArity :: Con -> Int
    valueArity typ = case locatedValue typ of
      TFun _ range -> 1 + valueArity range
      TCFun _ _ _ body -> valueArity body
      TDisjoint _ _ body -> valueArity body
      TKFun _ body -> valueArity body
      _ -> 0
    returnsTransaction :: Con -> Bool
    returnsTransaction typ = case locatedValue typ of
      TFun _ range -> returnsTransaction range
      TCFun _ _ _ body -> returnsTransaction body
      TDisjoint _ _ body -> returnsTransaction body
      TKFun _ body -> returnsTransaction body
      CApp function _ -> case locatedValue function of
        CModProj _ _ "transaction" -> True
        CNamed identifier -> Set.member identifier transactionConstructorIds
        _ -> False
      _ -> False

loadJavaScriptFiles :: ProjectPlan -> IO (Either [Diagnostic] [String])
loadJavaScriptFiles plan = do
  loaded <- mapM load directives
  let problems = [problem | Left problem <- loaded]
  pure $ if null problems then Right [script | Right script <- loaded] else Left problems
  where
    directives = filter ((== "jsFile") . projectDirectiveName) (projectDirectives plan)
    load directive = do
      let source = normalise
            (takeDirectory (spanFile (projectDirectiveSpan directive))
              </> projectDirectiveArgument directive)
      bytes <- try (BS.readFile source) :: IO (Either IOException BS.ByteString)
      pure $ case bytes of
        Left problem -> Left (diagnostic BackendPhase "javascript-file" (projectDirectiveSpan directive)
          ("Unable to read JavaScript file " <> source <> ": " <> show problem))
        Right contents -> Right (B8.unpack contents)

checkProject :: FilePath -> FilePath -> IO (Either [Diagnostic] ())
checkProject root target = fmap (fmap (const ())) (elaborateProject root target)

-- | Check a project against Vr's vendored Ur/Web compatibility profile.
checkBundledProject :: FilePath -> IO (Either [Diagnostic] ())
checkBundledProject target = fmap (fmap (const ())) (elaborateBundledProject target)

parseUnit :: ProjectUnit -> IO (Either [Diagnostic] ParsedUnit)
parseUnit unit = do
  implementationBytes <- BS.readFile (projectUnitImplementation unit)
  signatureResult <- case projectUnitSignature unit of
    Nothing -> pure (Right Nothing)
    Just signatureFile -> fmap Just <$> (parseSignature signatureFile <$> BS.readFile signatureFile)
  let implementationResult = parseImplementation (projectUnitImplementation unit) implementationBytes
  pure $ case (signatureResult, implementationResult) of
    (Left signatureProblems, Left implementationProblems) -> Left (signatureProblems <> implementationProblems)
    (Left signatureProblems, _) -> Left signatureProblems
    (_, Left implementationProblems) -> Left implementationProblems
    (Right signature, Right implementation) ->
      Right
        ParsedUnit
          { parsedUnitProject = unit
          , parsedUnitSignature = signature
          , parsedUnitImplementation = implementation
          }

unitDeclaration :: ParsedUnit -> SDecl
unitDeclaration unit =
  let projectUnit = parsedUnitProject unit
      implementationFile = projectUnitImplementation projectUnit
      at = fileSpan implementationFile
      signature = fmap (Located at . SSigConst) (parsedUnitSignature unit)
      structure = Located at (SStrConst (parsedUnitImplementation unit))
      moduleName = case reverse (projectUnitModule projectUnit) of
        name : _ -> name
        [] -> moduleNameOf (projectUnitBase projectUnit)
   in Located at (SDStr moduleName signature Nothing structure False)

syntheticPrefix :: ProjectPlan -> SFile
syntheticPrefix plan = case firstDirective "database" plan of
  Nothing -> []
  Just directive -> [Located (projectDirectiveSpan directive) (SDDatabase (projectDirectiveArgument directive))]

syntheticSuffix :: ProjectPlan -> SFile
syntheticSuffix plan = onErrorDeclaration <> exportDeclaration
  where
    onErrorDeclaration = case lastDirective "onError" plan of
      Nothing -> []
      Just directive ->
        let pieces = splitOn '.' (projectDirectiveArgument directive)
         in case pieces of
              first : rest@(_ : _) ->
                [Located (projectDirectiveSpan directive) (SDOnError first (init rest) (last rest))]
              _ -> []
    exportDeclaration = case reverse (projectUnits plan) of
      [] -> []
      unit : _ ->
        let at = fileSpan (projectUnitImplementation unit)
         in [Located at (SDExport (modulePathStructure at (projectUnitModule unit)))]

modulePathStructure :: Span -> [String] -> SStructure
modulePathStructure at path = case path of
  [] -> Located at (SStrVar "")
  first : rest -> foldl (\structure name -> Located at (SStrProj structure name)) (Located at (SStrVar first)) rest

firstDirective :: String -> ProjectPlan -> Maybe ProjectDirective
firstDirective name = find ((== name) . projectDirectiveName) . projectDirectives

lastDirective :: String -> ProjectPlan -> Maybe ProjectDirective
lastDirective name = find ((== name) . projectDirectiveName) . reverse . projectDirectives

fileSpan :: FilePath -> Span
fileSpan file = Span file start start
  where
    start = SourcePos 0 1 0

renderDiagnostic :: Diagnostic -> String
renderDiagnostic problem =
  let at = diagnosticSpan problem
      start = spanStart at
   in spanFile at
        <> ":"
        <> show (sourceLine start)
        <> ":"
        <> show (sourceColumn start)
        <> ": "
        <> diagnosticMessage problem

splitOn :: Eq value => value -> [value] -> [[value]]
splitOn separator = foldr step [[]]
  where
    step value groups@(group : rest)
      | value == separator = [] : groups
      | otherwise = (value : group) : rest
    step _ [] = error "splitOn invariant"
