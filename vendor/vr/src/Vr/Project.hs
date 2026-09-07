{-# LANGUAGE DerivingStrategies #-}
module Vr.Project
  ( ProjectDirective (..)
  , ProjectAsset (..)
  , FilterKind (..)
  , FilterAction (..)
  , FilterRule (..)
  , PathKind (..)
  , PatternKind (..)
  , RewriteRule (..)
  , ProjectUnit (..)
  , ProjectPlan (..)
  , loadProject
  , loadProjectWithLibrary
  , moduleNameOf
  , projectFilterRules
  , projectRewriteRules
  , rewriteProjectPath
  ) where

import Control.Monad.State.Strict (StateT, evalStateT, get, modify')
import Control.Monad.IO.Class (liftIO)
import qualified Data.ByteString.Char8 as B8
import Data.Char (isAlpha, isAlphaNum, isSpace, toUpper)
import Data.List (dropWhileEnd, find)
import qualified Data.Set as Set
import System.Directory
  ( canonicalizePath
  , doesFileExist
  , makeAbsolute
  )
import System.FilePath
  ( (</>)
  , dropExtension
  , isAbsolute
  , normalise
  , takeBaseName
  , takeDirectory
  , takeExtension
  )
import Vr.Source
  ( Diagnostic (..)
  , DiagnosticPhase (ProjectPhase)
  , SourcePos (..)
  , Span (..)
  , diagnostic
  )

data ProjectDirective = ProjectDirective
  { projectDirectiveName :: !String
  , projectDirectiveArgument :: !String
  , projectDirectiveSpan :: !Span
  }
  deriving stock (Eq, Ord, Show)

-- | One static project asset after its source file has been read.  Loading
-- bytes is an IO-facing project concern; all backends consume the same URI,
-- MIME type, and immutable contents.
data ProjectAsset = ProjectAsset
  { projectAssetUri :: !B8.ByteString
  , projectAssetMime :: !B8.ByteString
  , projectAssetBytes :: !B8.ByteString
  }
  deriving stock (Eq, Show)

-- | Runtime capability namespace selected by an Ur/Web @allow@ or @deny@
-- project directive.
data FilterKind
  = FilterUrl
  | FilterMime
  | FilterRequestHeader
  | FilterResponseHeader
  | FilterEnv
  | FilterMeta
  deriving stock (Eq, Ord, Show)

-- | Result of the first matching capability rule.
data FilterAction = FilterAllow | FilterDeny
  deriving stock (Eq, Ord, Show)

-- | One ordered capability rule.  Ur/Web tests rules in project-file order,
-- and the first matching rule decides the result.
data FilterRule = FilterRule
  { filterRuleKind :: !FilterKind
  , filterRuleAction :: !FilterAction
  , filterRulePatternKind :: !PatternKind
  , filterRulePattern :: !String
  }
  deriving stock (Eq, Ord, Show)

-- | Namespace selected by a @rewrite@ project directive.  Relation rules
-- match tables, views, and sequences as well as the relation namespace
-- itself, exactly as in Ur/Web's Settings module.
data PathKind
  = AnyPath
  | UrlPath
  | TablePath
  | SequencePath
  | ViewPath
  | RelationPath
  | CookiePath
  | StylePath
  deriving stock (Eq, Ord, Show)

-- | Whether a rewrite's source text must match the whole compiler path or
-- only its prefix.  A trailing @*@ in a project file denotes 'PrefixPattern'.
data PatternKind = ExactPattern | PrefixPattern
  deriving stock (Eq, Ord, Show)

-- | Parsed form of one Ur/Web path rewrite.  Rules retain project-file order,
-- the first match wins, and rewrites are never applied repeatedly.
data RewriteRule = RewriteRule
  { rewritePathKind :: !PathKind
  , rewritePatternKind :: !PatternKind
  , rewriteFrom :: !String
  , rewriteTo :: !String
  , rewriteHyphenate :: !Bool
  }
  deriving stock (Eq, Ord, Show)

data ProjectUnit = ProjectUnit
  { projectUnitBase :: !FilePath
  , projectUnitModule :: ![String]
  , projectUnitImplementation :: !FilePath
  , projectUnitSignature :: !(Maybe FilePath)
  }
  deriving stock (Eq, Ord, Show)

data ProjectPlan = ProjectPlan
  { projectTarget :: !FilePath
  , projectRoot :: !FilePath
  , projectDirectives :: ![ProjectDirective]
  , projectUnits :: ![ProjectUnit]
  , projectLibraries :: ![FilePath]
  }
  deriving stock (Eq, Ord, Show)

data ProjectLine = ProjectLine
  { lineSpan :: !Span
  , lineContent :: !(Maybe String)
  }
  deriving stock (Eq, Show)

type SeenLibraries = Set.Set FilePath

loadProject :: FilePath -> IO (Either [Diagnostic] ProjectPlan)
loadProject = loadProjectWithLibrary Nothing

-- | Load a project with the standard Ur library available through the
-- built-in empty @$@ path alias used by Ur/Web project files (for example,
-- @$/list@).
loadProjectWithLibrary :: Maybe FilePath -> FilePath -> IO (Either [Diagnostic] ProjectPlan)
loadProjectWithLibrary standardLibrary target = do
  resolved <- resolveTarget target
  case resolved of
    Left problem -> pure (Left [problem])
    Right (ProjectSingle urFile) -> loadSingle urFile
    Right (ProjectDescription urpFile) ->
      evalStateT (loadDescription standardLibrary urpFile) Set.empty

data Target = ProjectSingle FilePath | ProjectDescription FilePath

resolveTarget :: FilePath -> IO (Either Diagnostic Target)
resolveTarget rawTarget = do
  absolute <- makeAbsolute rawTarget
  let target = normalise absolute
      extension = takeExtension target
      urCandidate = if extension == ".ur" then target else target <> ".ur"
      urpCandidate = if extension == ".urp" then target else target <> ".urp"
  exactExists <- doesFileExist target
  urExists <- doesFileExist urCandidate
  urpExists <- doesFileExist urpCandidate
  pure $ case () of
    _ | extension == ".ur" && exactExists -> Right (ProjectSingle target)
      | extension == ".urp" && exactExists -> Right (ProjectDescription target)
      | extension == ".urs" -> Left (projectError target "project-target" "A .urs signature is not a project target")
      | urpExists -> Right (ProjectDescription urpCandidate)
      | urExists -> Right (ProjectSingle urCandidate)
      | exactExists && extension == ".ur" -> Right (ProjectSingle target)
      | otherwise -> Left (projectError target "missing-project" ("No Ur source or project exists for " <> rawTarget))

loadSingle :: FilePath -> IO (Either [Diagnostic] ProjectPlan)
loadSingle urFile = do
  absolute <- canonicalizePath urFile
  unitResult <- makeUnit (dropExtension absolute)
  pure $ case unitResult of
    Left problems -> Left problems
    Right unit ->
      Right
        ProjectPlan
          { projectTarget = absolute
          , projectRoot = takeDirectory absolute
          , projectDirectives = []
          , projectUnits = [unit]
          , projectLibraries = []
          }

loadDescription :: Maybe FilePath -> FilePath -> StateT SeenLibraries IO (Either [Diagnostic] ProjectPlan)
loadDescription standardLibrary urpFile = do
  absolute <- liftCanonical urpFile
  seen <- get
  if Set.member absolute seen
    then
      pure
        ( Right
            ProjectPlan
              { projectTarget = absolute
              , projectRoot = takeDirectory absolute
              , projectDirectives = []
              , projectUnits = []
              , projectLibraries = []
              }
        )
    else do
      modify' (Set.insert absolute)
      bytes <- liftRead absolute
      case bytes of
        Left problem -> pure (Left [problem])
        Right contents -> do
          let allLines = projectLines absolute contents
              meaningful = [content | ProjectLine _ (Just content) <- allLines]
              hasConfiguration = any looksLikeConfiguration meaningful
              (directiveLines, sourceLines) = partitionProject hasConfiguration allLines
              (directives, parseProblems) = parseDirectives directiveLines
              root = takeDirectory absolute
              aliases = maybe [] (\library -> [("", normalise library)]) standardLibrary <> collectPathAliases root directives
              libraryArguments = map projectDirectiveArgument (filter ((== "library") . projectDirectiveName) directives)
          libraries <- mapM (resolveLibrary root aliases) libraryArguments
          loadedLibraries <- mapM (loadDescription standardLibrary) libraries
          localUnits <- liftUnits root aliases sourceLines
          pure (assemblePlan absolute root directives libraries parseProblems loadedLibraries localUnits)

assemblePlan
  :: FilePath
  -> FilePath
  -> [ProjectDirective]
  -> [FilePath]
  -> [Diagnostic]
  -> [Either [Diagnostic] ProjectPlan]
  -> Either [Diagnostic] [ProjectUnit]
  -> Either [Diagnostic] ProjectPlan
assemblePlan target root directives libraries directProblems loadedLibraries localUnits =
  let libraryProblems = concat [libraryErrors | Left libraryErrors <- loadedLibraries]
      localProblems = either id (const []) localUnits
      problems = directProblems <> libraryProblems <> localProblems
      libraryUnits = concat [projectUnits plan | Right plan <- loadedLibraries]
      ownUnits = either (const []) id localUnits
      units = deduplicateUnits (libraryUnits <> ownUnits)
      nestedLibraries = concat [projectLibraries plan | Right plan <- loadedLibraries]
   in if null problems
        then
          Right
            ProjectPlan
              { projectTarget = target
              , projectRoot = root
              , projectDirectives = concat [projectDirectives plan | Right plan <- loadedLibraries] <> directives
              , projectUnits = units
              , projectLibraries = deduplicate (nestedLibraries <> libraries)
              }
        else Left problems

partitionProject :: Bool -> [ProjectLine] -> ([ProjectLine], [ProjectLine])
partitionProject False lines' = ([], filter hasNonBlankContent lines')
partitionProject True lines' =
  let (before, after) = break isBlank lines'
   in (filter hasContent before, filter hasNonBlankContent (drop 1 after))
  where
    isBlank (ProjectLine _ (Just "")) = True
    isBlank _ = False

hasContent :: ProjectLine -> Bool
hasContent (ProjectLine _ Nothing) = False
hasContent _ = True

hasNonBlankContent :: ProjectLine -> Bool
hasNonBlankContent (ProjectLine _ (Just content)) = any (not . isSpace) content
hasNonBlankContent _ = False

looksLikeConfiguration :: String -> Bool
looksLikeConfiguration content =
  content `elem` flagDirectives || any (`elem` [' ', '\t']) content

flagDirectives :: [String]
flagDirectives =
  [ "debug", "profile", "html5", "xhtml", "noMangleSql", "lessSafeFfi"
  , "safeGetDefault"
  ]

parseDirectives :: [ProjectLine] -> ([ProjectDirective], [Diagnostic])
parseDirectives = foldl' step ([], [])
  where
    step (directives, problems) (ProjectLine at maybeContent) =
      case maybeContent of
        Nothing -> (directives, problems)
        Just content ->
          let (name, rest) = break isSpace content
              argument = trim rest
              directive = ProjectDirective name argument at
              newProblems = validateDirective directive
           in (directives <> [directive], problems <> newProblems)

knownDirectives :: Set.Set String
knownDirectives =
  Set.fromList
    [ "prefix", "database", "dbms", "sigfile", "filecache", "exe", "sql"
    , "debug", "profile", "timeout", "ffi", "link", "linker", "include"
    , "script", "clientToServer", "safeGetDefault", "safeGet", "effectful"
    , "benignEffectful", "clientOnly", "serverOnly", "jsModule", "jsFunc"
    , "rewrite", "allow", "deny", "library", "path", "onError", "limit"
    , "minHeap", "coreInline", "monoInline", "alwaysInline", "neverInline"
    , "noXsrfProtection", "timeFormat", "noMangleSql", "html5", "xhtml"
    , "lessSafeFfi", "mimeTypes", "file", "jsFile"
    ]

validateDirective :: ProjectDirective -> [Diagnostic]
validateDirective directive
  | not (Set.member name knownDirectives) = [problem "unknown-directive" ("Unrecognized command '" <> name <> "'")]
  | name `elem` ["clientToServer", "effectful", "benignEffectful", "clientOnly", "serverOnly"]
      && not (isModuleMember argument) = [problem "ffi-reference" (name <> " argument is not Module.member")]
  | name == "jsFunc" && not (isJsMapping argument) = [problem "js-mapping" "jsFunc argument is not Module.member=javascriptName"]
  | name == "path" && not (isAssignment argument) = [problem "path-mapping" "path argument is not name=directory"]
  | name == "onError" && length (splitOn '.' argument) < 2 = [problem "on-error" "onError argument is not a qualified value"]
  | name `elem` ["timeout", "minHeap", "coreInline", "monoInline"] && not (isInteger argument) = [problem "integer-argument" (name <> " requires an integer")]
  | name == "minHeap" && not (isNonnegativeInteger argument) = [problem "min-heap" "minHeap requires a nonnegative integer"]
  | name == "limit" && not (validLimit argument) = [problem "limit" "limit requires a class and a nonnegative integer"]
  | name `elem` ["allow", "deny"] && not (validFilter argument) = [problem "filter" ("Bad '" <> name <> "' syntax")]
  | name == "rewrite" && not (validRewrite argument) = [problem "rewrite" "Bad 'rewrite' syntax"]
  | name == "file" && not (length (words argument) `elem` [2, 3]) = [problem "file" "file requires URI, filename, and optional MIME type"]
  | otherwise = []
  where
    name = projectDirectiveName directive
    argument = projectDirectiveArgument directive
    problem code message = diagnostic ProjectPhase code (projectDirectiveSpan directive) message

validFilter :: String -> Bool
validFilter argument =
  case words argument of
    [kind, _] -> kind `elem` ["url", "mime", "requestHeader", "responseHeader", "env", "meta"]
    _ -> False

validRewrite :: String -> Bool
validRewrite argument =
  case words argument of
    [kind, _] -> validPathKind kind
    [kind, _, _] -> validPathKind kind
    [kind, _, _, "[-]"] -> validPathKind kind
    _ -> False

validPathKind :: String -> Bool
validPathKind kind = kind `elem` ["all", "url", "table", "sequence", "view", "relation", "cookie", "style"]

-- | Construct the effective capability policy exactly as the reference
-- project loader does: textual order is preserved, every static-file URI is
-- allowed exactly at its directive position, and pure-fragment URLs are
-- allowed as the final fallback.
projectFilterRules :: ProjectPlan -> [FilterRule]
projectFilterRules plan =
  [ rule
  | directive <- projectDirectives plan
  , Just rule <- [directiveRule directive]
  ]
    <> [FilterRule FilterUrl FilterAllow PrefixPattern "#"]
  where
    directiveRule directive
      | projectDirectiveName directive `elem` ["allow", "deny"] =
          case words (projectDirectiveArgument directive) of
            [kindName, rawPattern] -> do
              kind <- parseFilterKind kindName
              let action =
                    if projectDirectiveName directive == "allow"
                      then FilterAllow
                      else FilterDeny
                  (patternKind, pattern') = case reverse rawPattern of
                    '*' : rest -> (PrefixPattern, reverse rest)
                    _ -> (ExactPattern, rawPattern)
              pure (FilterRule kind action patternKind pattern')
            _ -> Nothing
      | projectDirectiveName directive == "file" =
          case words (projectDirectiveArgument directive) of
            uri : _ -> Just (FilterRule FilterUrl FilterAllow ExactPattern uri)
            _ -> Nothing
      | otherwise = Nothing

    parseFilterKind name = case name of
      "url" -> Just FilterUrl
      "mime" -> Just FilterMime
      "requestHeader" -> Just FilterRequestHeader
      "responseHeader" -> Just FilterResponseHeader
      "env" -> Just FilterEnv
      "meta" -> Just FilterMeta
      _ -> Nothing

-- | Parse every validated @rewrite@ directive in effective matching order.
-- The reference loader restores textual order before installing the rules.
projectRewriteRules :: ProjectPlan -> [RewriteRule]
projectRewriteRules plan =
  [ rule
  | directive <- projectDirectives plan
  , projectDirectiveName directive == "rewrite"
  , Just rule <- [parseRewriteRule (projectDirectiveArgument directive)]
  ]

-- | Apply the first rewrite whose namespace and exact/prefix pattern match.
-- This is deliberately a single rewrite, not a rewriting loop.
rewriteProjectPath :: [RewriteRule] -> PathKind -> String -> String
rewriteProjectPath rules kind original = go rules
  where
    go [] = original
    go (rule : rest)
      | pathKindSubsumes kind (rewritePathKind rule)
      , Just suffix <- matchRule rule original =
          let rewritten = rewriteTo rule <> suffix
           in if rewriteHyphenate rule then map hyphenate rewritten else rewritten
      | otherwise = go rest
    hyphenate '_' = '-'
    hyphenate character = character

parseRewriteRule :: String -> Maybe RewriteRule
parseRewriteRule argument = case words argument of
  [kind, from] -> makeRule kind from "" False
  [kind, from, "[-]"] -> makeRule kind from "" True
  [kind, from, destination] -> makeRule kind from destination False
  [kind, from, destination, "[-]"] -> makeRule kind from destination True
  _ -> Nothing
  where
    makeRule kind from destination hyphenate = do
      pathKind <- parsePathKind kind
      let (patternKind, source) = case reverse from of
            '*' : reversed -> (PrefixPattern, reverse reversed)
            _ -> (ExactPattern, from)
      pure RewriteRule
        { rewritePathKind = pathKind
        , rewritePatternKind = patternKind
        , rewriteFrom = source
        , rewriteTo = destination
        , rewriteHyphenate = hyphenate
        }

parsePathKind :: String -> Maybe PathKind
parsePathKind name = case name of
  "all" -> Just AnyPath
  "url" -> Just UrlPath
  "table" -> Just TablePath
  "sequence" -> Just SequencePath
  "view" -> Just ViewPath
  "relation" -> Just RelationPath
  "cookie" -> Just CookiePath
  "style" -> Just StylePath
  _ -> Nothing

matchRule :: RewriteRule -> String -> Maybe String
matchRule rule value = case rewritePatternKind rule of
  ExactPattern
    | rewriteFrom rule == value -> Just ""
    | otherwise -> Nothing
  PrefixPattern -> stripPrefix (rewriteFrom rule) value

pathKindSubsumes :: PathKind -> PathKind -> Bool
pathKindSubsumes actual patternKind =
  actual == patternKind
    || patternKind == AnyPath
    || patternKind == RelationPath && actual `elem` [TablePath, SequencePath, ViewPath]

stripPrefix :: Eq value => [value] -> [value] -> Maybe [value]
stripPrefix [] values = Just values
stripPrefix _ [] = Nothing
stripPrefix (wanted : wantedRest) (actual : actualRest)
  | wanted == actual = stripPrefix wantedRest actualRest
  | otherwise = Nothing

validLimit :: String -> Bool
validLimit argument =
  case words argument of
    [category, number] | category `elem` limitCategories -> case (reads number :: [(Integer, String)]) of
      [(value, "")] -> value >= 0 && value <= toInteger (maxBound :: Int)
      _ -> False
    _ -> False

limitCategories :: [String]
limitCategories =
  [ "messages", "clients", "headers", "page", "heap", "script"
  , "inputs", "subinputs", "cleanup", "deltas", "transactionals"
  , "globals", "database", "time"
  ]

isInteger :: String -> Bool
isInteger value = case (reads value :: [(Integer, String)]) of
  [(_, "")] -> True
  _ -> False

isNonnegativeInteger :: String -> Bool
isNonnegativeInteger value = case (reads value :: [(Integer, String)]) of
  [(number, "")] -> number >= 0
  _ -> False

isModuleMember :: String -> Bool
isModuleMember value = case splitOn '.' value of
  [modName, member] -> not (null modName) && not (null member)
  _ -> False

isJsMapping :: String -> Bool
isJsMapping value = case break (== '=') value of
  (source, '=' : destination) -> isModuleMember (trim source) && not (null (trim destination))
  _ -> False

isAssignment :: String -> Bool
isAssignment value = case break (== '=') value of
  (name, '=' : directory) -> not (null name) && not (null directory)
  _ -> False

collectPathAliases :: FilePath -> [ProjectDirective] -> [(String, FilePath)]
collectPathAliases root = foldl' collect []
  where
    collect aliases directive
      | projectDirectiveName directive /= "path" = aliases
      | otherwise = case break (== '=') (projectDirectiveArgument directive) of
          (name, '=' : value) -> aliases <> [(name, absoluteFrom root value)]
          _ -> aliases

resolveLibrary :: FilePath -> [(String, FilePath)] -> String -> StateT SeenLibraries IO FilePath
resolveLibrary root aliases raw = do
  let base = absoluteFrom root (expandAlias aliases raw)
      direct = normalise (if takeExtension base == ".urp" then base else base <> ".urp")
      fallback = normalise (base </> "lib.urp")
  directExists <- liftIO' (doesFileExist direct)
  pure (if directExists then direct else fallback)

liftUnits :: FilePath -> [(String, FilePath)] -> [ProjectLine] -> StateT SeenLibraries IO (Either [Diagnostic] [ProjectUnit])
liftUnits root aliases lines' = do
  results <- mapM (liftUnit root aliases) lines'
  let problems = concat [errors | Left errors <- results]
  pure $ if null problems then Right [unit | Right unit <- results] else Left problems

liftUnit :: FilePath -> [(String, FilePath)] -> ProjectLine -> StateT SeenLibraries IO (Either [Diagnostic] ProjectUnit)
liftUnit root aliases (ProjectLine at maybeContent) = case maybeContent of
  Nothing -> pure (Left [diagnostic ProjectPhase "empty-source" at "Empty source entry"])
  Just content -> do
    let raw = trim content
        expanded = expandAlias aliases raw
        base0 = absoluteFrom root expanded
        base = case takeExtension base0 of
          ".ur" -> dropExtension base0
          ".urs" -> dropExtension base0
          _ -> base0
    result <- liftMakeUnit base
    pure $ case result of
      Left problems -> Left (map (relocate at) problems)
      Right unit -> Right unit

makeUnit :: FilePath -> IO (Either [Diagnostic] ProjectUnit)
makeUnit base = do
  absoluteBase <- makeAbsolute base
  let implementation = normalise (absoluteBase <> ".ur")
      signature = normalise (absoluteBase <> ".urs")
      fileName = takeBaseName absoluteBase
  implementationExists <- doesFileExist implementation
  signatureExists <- doesFileExist signature
  let nameProblems = validateModuleFileName implementation fileName
      missing = if implementationExists then [] else [projectError implementation "missing-source" ("Missing source file " <> implementation)]
      problems = nameProblems <> missing
      unit =
        ProjectUnit
          { projectUnitBase = normalise absoluteBase
          , projectUnitModule = [moduleNameOf fileName]
          , projectUnitImplementation = implementation
          , projectUnitSignature = if signatureExists then Just signature else Nothing
          }
  pure (if null problems then Right unit else Left problems)

validateModuleFileName :: FilePath -> String -> [Diagnostic]
validateModuleFileName path name = case name of
  [] -> [projectError path "module-name" "Empty module filename"]
  first : _
    | not (isAlpha first) -> [projectError path "module-name" ("Filename doesn't start with a letter: " <> name)]
    | any (\character -> not (isAlphaNum character) && character /= '_') name ->
        [projectError path "module-name" ("Filename contains a character that isn't alphanumeric or underscore: " <> name)]
    | otherwise -> []

moduleNameOf :: String -> String
moduleNameOf [] = []
moduleNameOf (first : rest) = toUpper first : rest

deduplicateUnits :: [ProjectUnit] -> [ProjectUnit]
deduplicateUnits = deduplicateOn projectUnitBase

deduplicate :: Ord a => [a] -> [a]
deduplicate = deduplicateOn id

deduplicateOn :: Ord key => (value -> key) -> [value] -> [value]
deduplicateOn key = reverse . snd . foldl' step (Set.empty, [])
  where
    step (seen, values) value
      | Set.member (key value) seen = (seen, values)
      | otherwise = (Set.insert (key value) seen, value : values)

projectLines :: FilePath -> B8.ByteString -> [ProjectLine]
projectLines file contents = go 0 1 chunks
  where
    split = B8.split '\n' contents
    chunks = if B8.isSuffixOf (B8.singleton '\n') contents && not (null split) then init split else split
    go _ _ [] = []
    go offset number (raw : rest) =
      let bytes = B8.unpack raw
          withoutCarriage = if not (null bytes) && last bytes == '\r' then init bytes else bytes
          content = classifyLine withoutCarriage
          end = SourcePos (offset + length withoutCarriage) number (length withoutCarriage)
          at = Span file (SourcePos offset number 0) end
       in ProjectLine at content : go (offset + B8.length raw + 1) (number + 1) rest

classifyLine :: String -> Maybe String
classifyLine raw =
  let (beforeHash, afterHash) = break (== '#') raw
   in if not (null afterHash) && all isSpace beforeHash
        then Nothing
        else Just (dropWhileEnd isSpace beforeHash)

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

splitOn :: Eq a => a -> [a] -> [[a]]
splitOn separator = foldr step [[]]
  where
    step value groups@(group : rest)
      | value == separator = [] : groups
      | otherwise = (value : group) : rest
    step _ [] = error "splitOn invariant"

expandAlias :: [(String, FilePath)] -> FilePath -> FilePath
expandAlias aliases ('$' : rest) =
  let (name, suffix) = break (== '/') rest
   in maybe ('$' : rest) (<> suffix) (lookupLatest name aliases)
expandAlias _ path = path

lookupLatest :: Eq key => key -> [(key, value)] -> Maybe value
lookupLatest key = fmap snd . find ((== key) . fst) . reverse

absoluteFrom :: FilePath -> FilePath -> FilePath
absoluteFrom root path
  | isAbsolute path = normalise path
  | otherwise = normalise (root </> path)

relocate :: Span -> Diagnostic -> Diagnostic
relocate at problem = problem {diagnosticSpan = at}

projectError :: FilePath -> String -> String -> Diagnostic
projectError file code message = diagnostic ProjectPhase code (Span file start start) message
  where
    start = SourcePos 0 1 0

liftCanonical :: FilePath -> StateT SeenLibraries IO FilePath
liftCanonical path = do
  exists <- liftIO' (doesFileExist path)
  if exists then liftIO' (canonicalizePath path) else liftIO' (makeAbsolute path)

liftRead :: FilePath -> StateT SeenLibraries IO (Either Diagnostic B8.ByteString)
liftRead path = do
  exists <- liftIO' (doesFileExist path)
  if exists
    then Right <$> liftIO' (B8.readFile path)
    else pure (Left (projectError path "missing-library" ("Missing project file " <> path)))

liftMakeUnit :: FilePath -> StateT SeenLibraries IO (Either [Diagnostic] ProjectUnit)
liftMakeUnit = liftIO' . makeUnit

liftIO' :: IO value -> StateT state IO value
liftIO' = liftIO
