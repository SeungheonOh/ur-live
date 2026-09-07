-- | Whole-program analyses that the reference compiler runs after Mono
-- lowering and before backend-specific code generation.  Keeping them in one
-- module makes the shared semantic boundary explicit without splitting a
-- handful of small fixed-point passes into separate packages.
module Vr.Mono.Analyze
  ( analyzeFile
  , analyzeFileWithFilters
  ) where

import Control.Monad.State.Strict (State, modify', runState)
import qualified Data.ByteString.Char8 as ByteString
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Vr.Middle
  ( DbMode (..)
  , ExportKind (..)
  , Sidedness (..)
  )
import qualified Vr.Mono.Syntax as M
import Vr.Project
  ( FilterAction (..)
  , FilterKind (..)
  , FilterRule (..)
  , PatternKind (..)
  )
import Vr.Source
  ( Diagnostic
  , DiagnosticPhase (MonoPhase)
  , Located (..)
  , Primitive (..)
  , Span
  , StringMode (..)
  , diagnostic
  )

-- | Analyze a standalone Mono file with Ur/Web's built-in fragment-URL rule.
analyzeFile :: M.File -> Either [Diagnostic] M.File
analyzeFile = analyzeFileWithFilters
  [FilterRule FilterUrl FilterAllow PrefixPattern "#"]

-- | Run the target-independent post-Mono passes: fold and validate literal
-- capabilities, reject duplicate runtime paths, and replace provisional
-- function modes with the classifications produced by Ur/Web's @ScriptCheck@
-- followed by @DbModeCheck@.
analyzeFileWithFilters :: [FilterRule] -> M.File -> Either [Diagnostic] M.File
analyzeFileWithFilters filters file =
  case problems of
    [] -> Right file
      { M.fileDeclarations = declarations
      , M.fileFunctionModes = databaseModes declarations (scriptModes declarations)
      }
    foundProblems -> Left foundProblems
  where
    (declarations, reversedCapabilityProblems) =
      runState (traverse (optimizeDeclaration filters) (M.fileDeclarations file)) []
    problems = pathProblems declarations <> reverse reversedCapabilityProblems

-- Literal capability optimization -------------------------------------------

type Optimize = State [Diagnostic]

optimizeDeclaration :: [FilterRule] -> M.Decl -> Optimize M.Decl
optimizeDeclaration filters (Located at declaration) = Located at <$> case declaration of
  M.DVal name identifier typ expression path ->
    M.DVal name identifier typ <$> optimizeExpression filters expression <*> pure path
  M.DValRec bindings -> M.DValRec <$> traverse optimizeBinding bindings
  M.DTable name fields primary constraints ->
    M.DTable name fields <$> optimizeExpression filters primary <*> optimizeExpression filters constraints
  M.DView name fields query -> M.DView name fields <$> optimizeExpression filters query
  M.DIndexDynamic table modes ->
    M.DIndexDynamic <$> optimizeExpression filters table <*> optimizeExpression filters modes
  M.DTask kind body -> M.DTask <$> optimizeExpression filters kind <*> optimizeExpression filters body
  M.DPolicy policy -> M.DPolicy <$> optimizePolicy filters policy
  M.DPolicyRaw expression -> M.DPolicyRaw <$> optimizeExpression filters expression
  other -> pure other
  where
    optimizeBinding (name, identifier, typ, expression, path) = do
      expression' <- optimizeExpression filters expression
      pure (name, identifier, typ, expression', path)

optimizePolicy :: [FilterRule] -> M.Policy -> Optimize M.Policy
optimizePolicy filters policy = case policy of
  M.PolicyClient expression -> M.PolicyClient <$> optimizeExpression filters expression
  M.PolicyInsert expression -> M.PolicyInsert <$> optimizeExpression filters expression
  M.PolicyDelete expression -> M.PolicyDelete <$> optimizeExpression filters expression
  M.PolicyUpdate expression -> M.PolicyUpdate <$> optimizeExpression filters expression
  M.PolicySequence expression -> M.PolicySequence <$> optimizeExpression filters expression

optimizeExpression :: [FilterRule] -> M.Expr -> Optimize M.Expr
optimizeExpression filters (Located at expression) = do
  rebuilt <- case expression of
    M.ECon kind constructor payload -> M.ECon kind constructor <$> traverse recurse payload
    M.ESome typ value -> M.ESome typ <$> recurse value
    M.EFfiApp moduleName member staticArguments arguments ->
      M.EFfiApp moduleName member staticArguments <$> traverse optimizeArgument arguments
    M.EApp function argument -> M.EApp <$> recurse function <*> recurse argument
    M.EAbs name argumentType resultType body -> M.EAbs name argumentType resultType <$> recurse body
    M.EStaticApp function argument -> M.EStaticApp <$> recurse function <*> pure argument
    M.EUnop operator value -> M.EUnop operator <$> recurse value
    M.EBinop intness operator left right -> M.EBinop intness operator <$> recurse left <*> recurse right
    M.ERecord fields -> M.ERecord <$> traverse optimizeField fields
    M.EField record field -> M.EField <$> recurse record <*> pure field
    M.ERecordConcat left right -> M.ERecordConcat <$> recurse left <*> recurse right
    M.ERecordCut record fields -> M.ERecordCut <$> recurse record <*> pure fields
    M.ECase scrutinee branches resultType scrutineeType ->
      M.ECase <$> recurse scrutinee <*> traverse optimizeBranch branches <*> pure resultType <*> pure scrutineeType
    M.EStrcat left right -> M.EStrcat <$> recurse left <*> recurse right
    M.EError value typ -> M.EError <$> recurse value <*> pure typ
    M.EReturnBlob content value typ -> M.EReturnBlob <$> traverse recurse content <*> recurse value <*> pure typ
    M.ERedirect value typ -> M.ERedirect <$> recurse value <*> pure typ
    M.EWrite value -> M.EWrite <$> recurse value
    M.ESeq first second -> M.ESeq <$> recurse first <*> recurse second
    M.ELet name typ value body -> M.ELet name typ <$> recurse value <*> recurse body
    M.EClosure identifier captures -> M.EClosure identifier <$> traverse recurse captures
    M.EQuery expressions tables stateType query body initial ->
      M.EQuery expressions tables stateType <$> recurse query <*> recurse body <*> recurse initial
    M.EDml value failureMode -> M.EDml <$> recurse value <*> pure failureMode
    M.ENextval value -> M.ENextval <$> recurse value
    M.ESetval sequence' value -> M.ESetval <$> recurse sequence' <*> recurse value
    M.EUnurlify value typ fromString -> M.EUnurlify <$> recurse value <*> pure typ <*> pure fromString
    M.EJavaScript mode value -> M.EJavaScript mode <$> recurse value
    M.ESignalReturn value -> M.ESignalReturn <$> recurse value
    M.ESignalBind signal continuation -> M.ESignalBind <$> recurse signal <*> recurse continuation
    M.ESignalSource value -> M.ESignalSource <$> recurse value
    M.EServerCall call typ effect failureMode ->
      M.EServerCall <$> recurse call <*> pure typ <*> pure effect <*> pure failureMode
    M.ERecv channel typ -> M.ERecv <$> recurse channel <*> pure typ
    M.ESleep value -> M.ESleep <$> recurse value
    M.ESpawn value -> M.ESpawn <$> recurse value
    leaf -> pure leaf
  optimizeLiteralCapability filters (Located at rebuilt)
  where
    recurse = optimizeExpression filters
    optimizeArgument (value, typ) = (,typ) <$> recurse value
    optimizeField (name, value, typ) = (name,,typ) <$> recurse value
    optimizeBranch (pattern, body) = (pattern,) <$> recurse body

optimizeLiteralCapability :: [FilterRule] -> M.Expr -> Optimize M.Expr
optimizeLiteralCapability filters expression@(Located at node) = case node of
  M.EPrim (PrimString HtmlString bytes) ->
    pure (Located at (M.EPrim (PrimString HtmlString (collapseHtmlWhitespace bytes))))
  M.EFfiApp "Basis" "htmlifyString" _ [(argument, _)]
    | Just bytes <- literalString argument ->
        pure (Located at (M.EPrim (PrimString HtmlString (htmlifyLiteral bytes))))
  M.EFfiApp "Basis" "strcat" _ [(left, _), (right, _)] ->
    pure (foldStringConcat at left right)
  M.EStrcat left right -> pure (foldStringConcat at left right)
  M.ESeq first second -> pure (foldOutputSequence at first second)
  M.EFfiApp "Basis" member _ [(argument, argumentType)]
    | Just bytes <- literalString argument ->
        optimizeLiteralOperation filters expression at member argument argumentType bytes
  M.EApp function argument
    | Just member <- basisFfiMember function
    , Just bytes <- literalString argument ->
        let argumentType = Located (locatedSpan argument) (M.TFfi "Basis" "string")
         in optimizeLiteralOperation filters expression at member argument argumentType bytes
  _ -> pure expression

-- Ur/Web treats whitespace written directly in XML as layout rather than as
-- a byte-for-byte string literal.  Each run is represented by its first byte;
-- adjacent XML literals are then joined without introducing a second space at
-- the concatenation boundary.
collapseHtmlWhitespace :: ByteString.ByteString -> ByteString.ByteString
collapseHtmlWhitespace = ByteString.pack . reverse . snd
  . ByteString.foldl' step (False, [])
  where
    step (previousWasSpace, bytes) byte
      | currentIsSpace && previousWasSpace = (True, bytes)
      | otherwise = (currentIsSpace, byte : bytes)
      where
        currentIsSpace = htmlSpace byte

foldStringConcat :: Span -> M.Expr -> M.Expr -> M.Expr
foldStringConcat at left right = case (locatedValue left, locatedValue right) of
  (M.EPrim (PrimString _ leftBytes), _) | ByteString.null leftBytes -> right
  (_, M.EPrim (PrimString _ rightBytes)) | ByteString.null rightBytes -> left
  (M.EPrim leftPrimitive@(PrimString _ _), M.EPrim rightPrimitive@(PrimString _ _)) ->
    Located at (M.EPrim (joinStringPrimitives leftPrimitive rightPrimitive))
  ( M.EPrim leftPrimitive@(PrimString _ _)
    , M.EStrcat nestedLeft@(Located _ (M.EPrim rightPrimitive@(PrimString _ _))) rest
    ) -> Located at (M.EStrcat
      (nestedLeft {locatedValue = M.EPrim (joinStringPrimitives leftPrimitive rightPrimitive)})
      rest)
  -- Keep concatenations right-associated, as MonoOpt does.  Besides making
  -- later writing linear, this exposes literal pairs that meet where a
  -- specialized fold substituted its accumulated XML value.
  (M.EStrcat first second, _) ->
    foldStringConcat at first (foldStringConcat at second right)
  _ -> Located at (M.EStrcat left right)

foldOutputSequence :: Span -> M.Expr -> M.Expr -> M.Expr
foldOutputSequence at first second = rebuild (merge (flatten first <> flatten second))
  where
    flatten value = case locatedValue value of
      M.ESeq left right -> flatten left <> flatten right
      _ | outputNoOp value -> []
      _ -> [value]

    merge (left : right : rest)
      | Just leftPrimitive <- writtenPrimitive left
      , Just rightPrimitive <- writtenPrimitive right =
          merge (writtenAt left
            (joinStringPrimitives leftPrimitive rightPrimitive) : rest)
      | otherwise = left : merge (right : rest)
    merge values = values

    rebuild values = case values of
      [] -> Located at (M.ERecord [])
      [only] -> only
      value : rest -> Located at (M.ESeq value (rebuild rest))

writtenPrimitive :: M.Expr -> Maybe Primitive
writtenPrimitive (Located _ expression) = case expression of
  M.EWrite (Located _ (M.EPrim primitive@PrimString {})) -> Just primitive
  _ -> Nothing

writtenAt :: M.Expr -> Primitive -> M.Expr
writtenAt (Located at _) primitive = Located at
  (M.EWrite (Located at (M.EPrim primitive)))

outputNoOp :: M.Expr -> Bool
outputNoOp (Located _ expression) = case expression of
  M.ERecord [] -> True
  M.EWrite (Located _ (M.EPrim (PrimString _ bytes))) -> ByteString.null bytes
  _ -> False

joinStringPrimitives :: Primitive -> Primitive -> Primitive
joinStringPrimitives (PrimString HtmlString left) (PrimString HtmlString right) =
  PrimString HtmlString (joinHtmlBytes left right)
joinStringPrimitives (PrimString _ left) (PrimString _ right) =
  PrimString NormalString (left <> right)
joinStringPrimitives left _ = left

joinHtmlBytes :: ByteString.ByteString -> ByteString.ByteString -> ByteString.ByteString
joinHtmlBytes left right
  | not (ByteString.null left)
  , not (ByteString.null right)
  , htmlSpace (ByteString.last left)
  , htmlSpace (ByteString.head right) = left <> ByteString.tail right
  | otherwise = left <> right

htmlSpace :: Char -> Bool
htmlSpace byte = byte `elem` [' ', '\t', '\n', '\r', '\f', '\v']

htmlifyLiteral :: ByteString.ByteString -> ByteString.ByteString
htmlifyLiteral = ByteString.concatMap escape
  where
    escape '<' = ByteString.pack "&lt;"
    escape '&' = ByteString.pack "&amp;"
    escape byte = ByteString.singleton byte

basisFfiMember :: M.Expr -> Maybe String
basisFfiMember (Located _ expression) = case expression of
  M.EFfi "Basis" member _ -> Just member
  _ -> Nothing

optimizeLiteralOperation
  :: [FilterRule]
  -> M.Expr
  -> Span
  -> String
  -> M.Expr
  -> M.Type
  -> ByteString.ByteString
  -> Optimize M.Expr
optimizeLiteralOperation filters original at member argument argumentType bytes = case member of
  "blessData" -> blessLiteral at argument (validData bytes)
    ("Invalid HTML5 data-* attribute " <> ByteString.unpack bytes)
  "bless" -> blessLiteral at argument (validUrl bytes && filterAllows filters FilterUrl bytes)
    ("Invalid URL " <> ByteString.unpack bytes <> " passed to 'bless'")
  "checkUrl" -> pure (checked (validUrl bytes && filterAllows filters FilterUrl bytes) argumentType argument)
  "blessMime" -> blessLiteral at argument (validMime bytes && filterAllows filters FilterMime bytes)
    (invalidString "blessMime" bytes)
  "checkMime" -> pure (checked (validMime bytes && filterAllows filters FilterMime bytes) argumentType argument)
  "atom" -> blessLiteral at argument (validAtom bytes) (invalidString "atom" bytes)
  "css_url" -> blessLiteral at argument (validCssUrl bytes)
    ("Invalid URL " <> ByteString.unpack bytes <> " passed to 'css_url'")
  "property" -> blessLiteral at argument (validProperty bytes) (invalidString "property" bytes)
  "blessRequestHeader" -> blessLiteral at argument (validMime bytes && filterAllows filters FilterRequestHeader bytes)
    (invalidString "blessRequestHeader" bytes)
  "checkRequestHeader" -> pure
    (checked (validMime bytes && filterAllows filters FilterRequestHeader bytes) argumentType argument)
  "blessResponseHeader" -> blessLiteral at argument (validMime bytes && filterAllows filters FilterResponseHeader bytes)
    (invalidString "blessResponseHeader" bytes)
  "checkResponseHeader" -> pure
    (checked (validMime bytes && filterAllows filters FilterResponseHeader bytes) argumentType argument)
  "blessEnvVar" -> blessLiteral at argument (validEnv bytes && filterAllows filters FilterEnv bytes)
    (invalidString "blessEnvVar" bytes)
  "checkEnvVar" -> pure
    (checked (validEnv bytes && filterAllows filters FilterEnv bytes) argumentType argument)
  "blessMeta" -> blessLiteral at argument (validMeta bytes && filterAllows filters FilterMeta bytes)
    (invalidString "blessMeta" bytes)
  "checkMeta" -> pure
    (checked (validMeta bytes && filterAllows filters FilterMeta bytes) argumentType argument)
  _ -> pure original

blessLiteral :: Span -> M.Expr -> Bool -> String -> Optimize M.Expr
blessLiteral at argument allowed message = do
  if allowed
    then pure ()
    else modify' (diagnostic MonoPhase "invalid-literal-capability" at message :)
  pure argument

literalString :: M.Expr -> Maybe ByteString.ByteString
literalString (Located _ value) = case value of
  M.EPrim (PrimString _ bytes) -> Just bytes
  _ -> Nothing

checked :: Bool -> M.Type -> M.Expr -> M.Expr
checked allowed argumentType argument
  | allowed = Located (locatedSpan argument) (M.ESome argumentType argument)
  | otherwise = Located (locatedSpan argument) (M.ENone argumentType)

invalidString :: String -> ByteString.ByteString -> String
invalidString operation bytes =
  "Invalid string " <> ByteString.unpack bytes <> " passed to '" <> operation <> "'"

filterAllows :: [FilterRule] -> FilterKind -> ByteString.ByteString -> Bool
filterAllows rules kind bytes = go rules
  where
    value = ByteString.unpack bytes
    go [] = False
    go (rule : rest)
      | filterRuleKind rule /= kind = go rest
      | ruleMatches rule value = filterRuleAction rule == FilterAllow
      | otherwise = go rest

ruleMatches :: FilterRule -> String -> Bool
ruleMatches rule value = case filterRulePatternKind rule of
  ExactPattern -> value == filterRulePattern rule
  PrefixPattern -> filterRulePattern rule `isPrefixOfString` value

isPrefixOfString :: String -> String -> Bool
isPrefixOfString [] _ = True
isPrefixOfString _ [] = False
isPrefixOfString (expected : rest) (actual : suffix) =
  expected == actual && isPrefixOfString rest suffix

validUrl, validData, validMime, validAtom, validCssUrl, validEnv, validMeta :: ByteString.ByteString -> Bool
validUrl = ByteString.all (\character -> character >= '!' && character <= '~')
validData = ByteString.all (\character -> asciiAlphaNum character || character `elem` "_-")
validMime = ByteString.all (\character -> asciiAlphaNum character || character `elem` "/-.+")
validAtom = ByteString.all (\character -> asciiAlphaNum character || character `elem` "+-.%#")
validCssUrl = ByteString.all (\character -> asciiAlphaNum character || character `elem` ":/._+-%?&=#")
validEnv = ByteString.all (\character -> asciiAlphaNum character || character `elem` "_.")
validMeta = ByteString.all (\character -> asciiAlpha character || character == '-')

validProperty :: ByteString.ByteString -> Bool
validProperty bytes = case ByteString.unpack bytes of
  first : rest ->
    (nameStart first || case rest of second : _ -> first == '-' && nameStart second; [] -> False)
      && all nameCharacter (first : rest)
  [] -> False
  where
    nameStart character = asciiAlpha character || character == '_'
    nameCharacter character = nameStart character || asciiDigit character || character == '-'

asciiAlphaNum, asciiAlpha, asciiDigit :: Char -> Bool
asciiAlphaNum character = asciiAlpha character || asciiDigit character
asciiAlpha character =
  (character >= 'A' && character <= 'Z') || (character >= 'a' && character <= 'z')
asciiDigit character = character >= '0' && character <= '9'

-- PathCheck ------------------------------------------------------------------

data Paths = Paths
  { functionPaths :: !(Set.Set String)
  , relationPaths :: !(Set.Set String)
  , cookiePaths :: !(Set.Set String)
  , stylePaths :: !(Set.Set String)
  , accumulatedProblems :: ![Diagnostic]
  }

emptyPaths :: Paths
emptyPaths = Paths Set.empty Set.empty Set.empty Set.empty []

pathProblems :: [M.Decl] -> [Diagnostic]
pathProblems = reverse . accumulatedProblems . foldl' check emptyPaths
  where
    check paths declaration = case locatedValue declaration of
      M.DExport _ path _ _ _ _ -> addFunction declaration path paths
      M.DTable path _ primary constraints ->
        let withRelation = addRelation declaration path paths
            withPrimary =
              if emptyString primary
                then withRelation
                else addRelation declaration (path <> "_Pkey") withRelation
         in foldl' (flip (addRelation declaration)) withPrimary (constraintPaths path constraints)
      M.DSequence path -> addRelation declaration path paths
      M.DCookie path -> addCookie declaration path paths
      M.DStyle path -> addStyle declaration path paths
      _ -> paths

addFunction :: M.Decl -> String -> Paths -> Paths
addFunction declaration path paths
  | Set.member path (functionPaths paths) =
      addProblem declaration "duplicate-function-path" ("Duplicate function path " <> path) paths
  | (shorter, longer) : _ <-
      [ if pathPrefix existing path then (existing, path) else (path, existing)
      | existing <- Set.toAscList (functionPaths paths)
      , pathPrefix existing path || pathPrefix path existing
      ] =
      addProblem declaration "conflicting-function-prefix"
        ("Conflicting URL prefixes for page handlers: \"" <> shorter
          <> "\" is a prefix of \"" <> longer <> "\".")
        paths
  | otherwise = paths {functionPaths = Set.insert path (functionPaths paths)}

pathPrefix :: String -> String -> Bool
pathPrefix prefix value =
  prefix `isPrefixOfString` value
    && case drop (length prefix) value of
      [] -> True
      '/' : _ -> True
      _ -> False

addRelation :: M.Decl -> String -> Paths -> Paths
addRelation declaration path paths
  | Set.member path (relationPaths paths) =
      addProblem declaration "duplicate-relation-path" ("Duplicate table/sequence path " <> path) paths
  | otherwise = paths {relationPaths = Set.insert path (relationPaths paths)}

addCookie :: M.Decl -> String -> Paths -> Paths
addCookie declaration path paths
  | Set.member path (cookiePaths paths) =
      addProblem declaration "duplicate-cookie-path" ("Duplicate cookie path " <> path) paths
  | otherwise = paths {cookiePaths = Set.insert path (cookiePaths paths)}

addStyle :: M.Decl -> String -> Paths -> Paths
addStyle declaration path paths
  | Set.member path (stylePaths paths) =
      addProblem declaration "duplicate-style-path" ("Duplicate style path " <> path) paths
  | otherwise = paths {stylePaths = Set.insert path (stylePaths paths)}

addProblem :: M.Decl -> String -> String -> Paths -> Paths
addProblem declaration code message paths =
  paths
    { accumulatedProblems =
        diagnostic MonoPhase code (locatedSpan declaration) message
          : accumulatedProblems paths
    }

emptyString :: M.Expr -> Bool
emptyString expression = case locatedValue expression of
  M.EPrim (PrimString _ bytes) -> ByteString.null bytes
  _ -> False

constraintPaths :: String -> M.Expr -> [String]
constraintPaths table expression = case locatedValue expression of
  M.ERecord [(M.StaticName name, _, _)] -> [table <> "_" <> name]
  M.EStrcat left right -> constraintPaths table left <> constraintPaths table right
  _ -> []

-- ScriptCheck ----------------------------------------------------------------

scriptModes :: [M.Decl] -> [(M.GlobalId, Sidedness, DbMode)]
scriptModes declarations =
  [ (identifier, placement identifier, DbModePending)
  | identifier <- Set.toAscList (Set.union pullIds pushIds)
  ]
  where
    rpcRoutes = Map.fromList
      [ (path, identifier)
      | declaration <- declarations
      , M.DExport (Rpc _) path identifier _ _ _ <- [locatedValue declaration]
      ]
    (pullIds, pushIds) = foldl' (classifyDeclaration rpcRoutes) (Set.empty, Set.empty) declarations
    placement identifier
      | Set.member identifier pushIds = ServerAndPullAndPush
      | otherwise = ServerAndPull

classifyDeclaration
  :: Map.Map String M.GlobalId
  -> (Set.Set M.GlobalId, Set.Set M.GlobalId)
  -> M.Decl
  -> (Set.Set M.GlobalId, Set.Set M.GlobalId)
classifyDeclaration rpcRoutes (pullIds, pushIds) declaration = case locatedValue declaration of
  M.DVal _ identifier _ expression _ ->
    ( addWhen (hasClient False rpcRoutes pullIds expression) identifier pullIds
    , addWhen (hasClient True rpcRoutes pushIds expression) identifier pushIds
    )
  M.DValRec bindings ->
    let pulls = any (hasClient False rpcRoutes pullIds . bindingExpression) bindings
        pushes = any (hasClient True rpcRoutes pushIds . bindingExpression) bindings
        identifiers = [identifier | (_, identifier, _, _, _) <- bindings]
     in (if pulls then foldr Set.insert pullIds identifiers else pullIds,
         if pushes then foldr Set.insert pushIds identifiers else pushIds)
  _ -> (pullIds, pushIds)
  where
    bindingExpression (_, _, _, expression, _) = expression
    addWhen condition identifier known = if condition then Set.insert identifier known else known

hasClient
  :: Bool
  -> Map.Map String M.GlobalId
  -> Set.Set M.GlobalId
  -> M.Expr
  -> Bool
hasClient push rpcRoutes clientIds = expressionAny clientNode
  where
    clientNode expression = case locatedValue expression of
      M.ERecv {} -> push
      M.EFfi "Basis" name _ -> basisClientNode name
      M.EFfiApp "Basis" name _ _ -> basisClientNode name
      M.EJavaScript {} -> not push
      -- Reference Monoize wraps client tag operands in EJavaScript before
      -- ScriptCheck.  Vr deliberately keeps the structured tag application
      -- until backend lowering, so recognize the equivalent client island at
      -- this shared boundary.  Its children are still traversed, which lets
      -- ERecv and other push roots classify the same handler independently.
      _ | not push && tagNeedsClient expression -> True
      M.ENamed identifier -> Set.member identifier clientIds
      M.EServerCall call _ _ _ -> case callHead call of
        Nothing -> True
        Just path -> maybe True (`Set.member` clientIds) (Map.lookup path rpcRoutes)
      _ -> False
    basisClientNode name
      | push = name `elem` ["new_channel", "channel", "self"]
      | otherwise = Set.member name browserOnlyBasis

-- Vr's Mono retains a seven-argument Basis.tag application.  Only its
-- attributes operand and dynClass/dynStyle operands are browser islands;
-- ordinary records may legitimately have fields named On*, Signal, or Code.
tagNeedsClient :: M.Expr -> Bool
tagNeedsClient expression = case collectApplications expression of
  (function, [_, dynamicClass, _, dynamicStyle, attributes, _, _])
    | M.EFfi "Basis" "tag" _ <- locatedValue function ->
        optionIsPresent dynamicClass || optionIsPresent dynamicStyle
          || case locatedValue attributes of
            M.ERecord fields -> any clientRecordField fields
            _ -> False
  _ -> False
  where
    optionIsPresent option = case locatedValue option of
      M.ESome {} -> True
      _ -> False
    clientRecordField (M.StaticName name, _, typ)
      | "On" `isPrefixOf` name = functionDepth typ >= 1
      | name == "Signal" = case locatedValue typ of
          M.TSignal {} -> True
          _ -> False
      | name == "Code" = case locatedValue typ of
          M.TFun {} -> True
          _ -> False
    clientRecordField _ = False

collectApplications :: M.Expr -> (M.Expr, [M.Expr])
collectApplications = go []
  where
    go arguments expression = case locatedValue expression of
      M.EApp function argument -> go (argument : arguments) function
      _ -> (expression, arguments)

functionDepth :: M.Type -> Int
functionDepth typ = case locatedValue typ of
  M.TFun _ range -> 1 + functionDepth range
  _ -> 0

browserOnlyBasis :: Set.Set String
browserOnlyBasis = Set.fromList
  [ "get_client_source", "current", "alert", "confirm", "recv", "sleep", "spawn"
  , "onError", "onFail", "onConnectFail", "onDisconnect", "onServerError"
  , "mouseEvent", "keyEvent", "onClick", "onContextmenu", "onDblclick"
  , "onKeydown", "onKeypress", "onKeyup", "onMousedown", "onMouseenter"
  , "onMouseleave", "onMousemove", "onMouseout", "onMouseover", "onMouseup"
  , "preventDefault", "stopPropagation", "giveFocus"
  ]

callHead :: M.Expr -> Maybe String
callHead expression = case locatedValue expression of
  M.EStrcat left _ -> callHead left
  M.EPrim (PrimString _ bytes) -> Just (ByteString.unpack bytes)
  _ -> Nothing

-- DbModeCheck ----------------------------------------------------------------

databaseModes
  :: [M.Decl]
  -> [(M.GlobalId, Sidedness, DbMode)]
  -> [(M.GlobalId, Sidedness, DbMode)]
databaseModes declarations placements = placed <> remaining
  where
    known = foldl' classifyDeclarationModes Map.empty declarations
    placed =
      [ (identifier, sidedness, Map.findWithDefault AnyDb identifier known)
      | (identifier, sidedness, _) <- placements
      ]
    placedIds = Set.fromList [identifier | (identifier, _, _) <- placements]
    remaining =
      [ (identifier, ServerOnly, mode)
      | (identifier, mode) <- Map.toAscList known
      , not (Set.member identifier placedIds)
      ]

classifyDeclarationModes
  :: Map.Map M.GlobalId DbMode
  -> M.Decl
  -> Map.Map M.GlobalId DbMode
classifyDeclarationModes known declaration = case locatedValue declaration of
  M.DVal _ identifier _ expression _ -> Map.insert identifier (expressionMode known expression) known
  M.DValRec bindings ->
    let mode =
          if any ((/= NoDb) . expressionMode known . bindingExpression) bindings
            then AnyDb
            else NoDb
     in foldl' (\m (_, identifier, _, _, _) -> Map.insert identifier mode m) known bindings
  _ -> known
  where
    bindingExpression (_, _, _, expression, _) = expression

expressionMode :: Map.Map M.GlobalId DbMode -> M.Expr -> DbMode
expressionMode known = expressionFold step NoDb
  where
    step mode expression = case locatedValue expression of
      M.EQuery {} -> mergeMode OneQuery mode
      M.EDml {} -> AnyDb
      M.ENextval {} -> AnyDb
      M.ESetval {} -> AnyDb
      M.EFfi "Basis" name _
        | name == "query" -> mergeMode OneQuery mode
        | name `elem` ["dml", "tryDml", "nextval", "setval"] -> AnyDb
      M.EFfiApp "Basis" name _ _
        | name == "query" -> mergeMode OneQuery mode
        | name `elem` ["dml", "tryDml", "nextval", "setval"] -> AnyDb
      M.ENamed identifier -> mergeMode (Map.findWithDefault NoDb identifier known) mode
      _ -> mode

mergeMode :: DbMode -> DbMode -> DbMode
mergeMode NoDb other = other
mergeMode other NoDb = other
mergeMode _ _ = AnyDb

-- Expression traversal -------------------------------------------------------

expressionAny :: (M.Expr -> Bool) -> M.Expr -> Bool
expressionAny predicate expression =
  predicate expression || any (expressionAny predicate) (expressionChildren expression)

expressionFold :: (value -> M.Expr -> value) -> value -> M.Expr -> value
expressionFold step initial expression =
  step (foldl' (expressionFold step) initial (expressionChildren expression)) expression

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
  M.EError value _ -> [value]
  M.EReturnBlob content value _ -> maybe [] pure content <> [value]
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
  M.EPrim {} -> []
  M.ERel {} -> []
  M.ENamed {} -> []
  M.ENone {} -> []
  M.EFfi {} -> []
