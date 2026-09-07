{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TupleSections #-}

-- | Ur/Web-compatible SQL-result cache instrumentation.
--
-- SQL caching is deliberately represented in target-independent Mono rather
-- than hidden inside either database adapter.  A cacheable query transaction
-- receives a stable site identity and an ordered key.  Database modifications
-- are then paired with the sites whose queries mention the modified table.
-- Direct queries use their ordered dynamic SQL injections as keys.  Ordinary
-- equality predicates are related symbolically to inserted, deleted, and
-- updated columns so the pass can emit selective invalidation prefixes.
-- Unsupported conflict shapes deliberately retain wildcard invalidation.
module Vr.Mono.SqlCache
  ( SqlCacheHeuristic (..)
  , parseHeuristic
  , instrumentFile
  ) where

import Control.Monad.State.Strict (State, get, modify', runState)
import qualified Data.ByteString.Char8 as ByteString
import Data.List (isInfixOf, nubBy)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Vr.Mono.Syntax as M
import Vr.Source
  ( Located (..)
  , Primitive (..)
  , SourcePos (..)
  , Span (..)
  , StringMode (NormalString)
  )

-- | Ur/Web's experimental @-heuristic@ choices.  Direct query candidates
-- satisfy every reference mode; the distinctions become observable when the
-- dependency pass combines a query with surrounding pure expressions.
data SqlCacheHeuristic
  = Smart
  | Always
  | Never
  | NoPureAll
  | NoPureOne
  | NoCombo
  deriving stock (Eq, Ord, Show)

parseHeuristic :: String -> Maybe SqlCacheHeuristic
parseHeuristic value = case value of
  "smart" -> Just Smart
  "always" -> Just Always
  "never" -> Just Never
  "nopureall" -> Just NoPureAll
  "nopureone" -> Just NoPureOne
  "nocombo" -> Just NoCombo
  _ -> Nothing

data CacheSite = CacheSite
  { cacheSiteIndex :: !Int
  , cacheSiteTables :: ![String]
  , cacheSiteKeys :: ![Maybe SqlField]
  }

-- | A physical database column used to relate a query argument to values
-- supplied by a later DML statement.  SQL aliases have already been resolved
-- by the time a value reaches this representation.
data SqlField = SqlField !String !String
  deriving stock (Eq, Ord, Show)

data QueryKey = QueryKey
  { queryKeyExpression :: !M.Expr
  , queryKeyField :: !(Maybe SqlField)
  }

data QueryDependency = QueryDependency
  { queryDependencyKeys :: ![QueryKey]
  , queryDependencyTables :: ![String]
  }

data FreePath = FreePath !Int ![String]
  deriving stock (Eq, Ord, Show)

data DmlAnalysis = DmlAnalysis
  { dmlAnalysisTable :: !(Maybe String)
  , dmlAnalysisRows :: ![Map.Map SqlField M.Expr]
  }

data TableEnvironment = TableEnvironment
  { tableEnvironmentNames :: ![String]
  , tableEnvironmentGlobals :: !(Map.Map M.GlobalId String)
  }

data QueryState = QueryState
  { queryNextIndex :: !Int
  , querySites :: ![CacheSite]
  }

instrumentFile :: SqlCacheHeuristic -> M.File -> M.File
instrumentFile heuristic file =
  fileWithQueries
    { M.fileDeclarations = map (flushDeclaration sites tableEnvironment)
        (M.fileDeclarations fileWithQueries)
    }
  where
    declarations = M.fileDeclarations file
    tables = [name | declaration <- declarations, M.DTable name _ _ _ <- [locatedValue declaration]]
    tableEnvironment = TableEnvironment tables (Map.fromList
      [ (identifier, ByteString.unpack bytes)
      | declaration <- declarations
      , M.DVal _ identifier _ expression _ <- [locatedValue declaration]
      , M.EPrim (PrimString _ bytes) <- [locatedValue expression]
      , ByteString.unpack bytes `elem` tables
      ])
    datatypes = Map.fromList
      [ (identifier, alternatives)
      | declaration <- declarations
      , M.DDatatype definitions <- [locatedValue declaration]
      , (_, identifier, alternatives) <- definitions
      ]
    globals = Map.fromList
      ([ (identifier, typ)
       | declaration <- declarations
       , M.DVal _ identifier typ _ _ <- [locatedValue declaration]
       ] <>
       [ (identifier, typ)
       | declaration <- declarations
       , M.DValRec bindings <- [locatedValue declaration]
       , (_, identifier, typ, _, _) <- bindings
       ])
    reachable = reachableGlobals declarations
    (instrumented, finalState) = runState
      (traverse (queryDeclaration heuristic datatypes globals reachable tableEnvironment) declarations)
      (QueryState 0 [])
    fileWithQueries = file {M.fileDeclarations = instrumented}
    sites = reverse (querySites finalState)

queryDeclaration
  :: SqlCacheHeuristic
  -> Map.Map M.GlobalId [(String, M.GlobalId, Maybe M.Type)]
  -> Map.Map M.GlobalId M.Type
  -> Set.Set M.GlobalId
  -> TableEnvironment
  -> M.Decl
  -> State QueryState M.Decl
queryDeclaration heuristic datatypes globals reachable tableEnvironment declaration = do
  value <- case locatedValue declaration of
    M.DVal name identifier typ expression path ->
      if Set.member identifier reachable
        then M.DVal name identifier typ <$> recurse [] (Just typ) expression <*> pure path
        else pure (M.DVal name identifier typ expression path)
    M.DValRec bindings -> M.DValRec <$> traverse binding bindings
    M.DTable name fields primary constraints ->
      M.DTable name fields <$> recurse [] Nothing primary <*> recurse [] Nothing constraints
    M.DView name fields query -> M.DView name fields <$> recurse [] Nothing query
    M.DIndexDynamic table modes -> M.DIndexDynamic
      <$> recurse [] Nothing table <*> recurse [] Nothing modes
    M.DTask schedule body -> M.DTask
      <$> recurse [] Nothing schedule <*> recurse [] Nothing body
    M.DPolicy policy -> M.DPolicy <$> policyExpression policy
    M.DPolicyRaw expression -> M.DPolicyRaw <$> recurse [] Nothing expression
    other -> pure other
  pure declaration {locatedValue = value}
  where
    recurse = cacheExpression heuristic datatypes globals tableEnvironment
    binding (name, identifier, typ, expression, path) =
      if Set.member identifier reachable
        then (name, identifier, typ,, path) <$> recurse [] (Just typ) expression
        else pure (name, identifier, typ, expression, path)
    policyExpression policy = case policy of
      M.PolicyClient expression -> M.PolicyClient <$> recurse [] Nothing expression
      M.PolicyInsert expression -> M.PolicyInsert <$> recurse [] Nothing expression
      M.PolicyDelete expression -> M.PolicyDelete <$> recurse [] Nothing expression
      M.PolicyUpdate expression -> M.PolicyUpdate <$> recurse [] Nothing expression
      M.PolicySequence expression -> M.PolicySequence <$> recurse [] Nothing expression

reachableGlobals :: [M.Decl] -> Set.Set M.GlobalId
reachableGlobals declarations = close initialRoots
  where
    definitions = Map.fromList
      ([ (identifier, expression)
       | declaration <- declarations
       , M.DVal _ identifier _ expression _ <- [locatedValue declaration]
       ] <>
       [ (identifier, expression)
       | declaration <- declarations
       , M.DValRec bindings <- [locatedValue declaration]
       , (_, identifier, _, expression, _) <- bindings
       ])
    initialRoots = Set.fromList (concatMap declarationRoots declarations)
    close found =
      let discovered = Set.unions
            [ expressionGlobals expression
            | identifier <- Set.toList found
            , Just expression <- [Map.lookup identifier definitions]
            ]
          next = Set.union found discovered
       in if next == found then found else close next

declarationRoots :: M.Decl -> [M.GlobalId]
declarationRoots declaration = case locatedValue declaration of
  M.DExport _ _ identifier _ _ _ -> [identifier]
  M.DDatabase info -> [M.databaseExpunge info, M.databaseInitialize info]
  M.DOnError identifier -> [identifier]
  M.DTable _ _ primary constraints ->
    Set.toList (Set.union (expressionGlobals primary) (expressionGlobals constraints))
  M.DView _ _ query -> Set.toList (expressionGlobals query)
  M.DIndexDynamic table modes ->
    Set.toList (Set.union (expressionGlobals table) (expressionGlobals modes))
  M.DTask schedule body ->
    Set.toList (Set.union (expressionGlobals schedule) (expressionGlobals body))
  M.DPolicy policy -> Set.toList (expressionGlobals (case policy of
    M.PolicyClient expression -> expression
    M.PolicyInsert expression -> expression
    M.PolicyDelete expression -> expression
    M.PolicyUpdate expression -> expression
    M.PolicySequence expression -> expression))
  M.DPolicyRaw expression -> Set.toList (expressionGlobals expression)
  _ -> []

expressionGlobals :: M.Expr -> Set.Set M.GlobalId
expressionGlobals expression = Set.union direct
  (Set.unions (map expressionGlobals (expressionChildren expression)))
  where
    direct = case locatedValue expression of
      M.ENamed identifier -> Set.singleton identifier
      M.EClosure identifier _ -> Set.singleton identifier
      _ -> Set.empty

cacheExpression
  :: SqlCacheHeuristic
  -> Map.Map M.GlobalId [(String, M.GlobalId, Maybe M.Type)]
  -> Map.Map M.GlobalId M.Type
  -> TableEnvironment
  -> [M.Type]
  -> Maybe M.Type
  -> M.Expr
  -> State QueryState M.Expr
cacheExpression heuristic datatypes globals tableEnvironment environment expected source =
  case cacheCandidate of
    Just (typ, keys, sites) -> registerCache typ keys sites source
    Nothing
      | isQueryExpression source -> pure source
      | otherwise -> descend
  where
    recurse = cacheExpression heuristic datatypes globals tableEnvironment
    inferred = case expected of
      Just typ -> Just typ
      Nothing -> case queryExpressionType source of
        Just typ -> Just typ
        Nothing -> inferExpressionType globals environment source
    cacheCandidate = do
      typ <- inferred
      if cacheableType datatypes typ && not (functionType typ)
        && worthCaching source && safeExpression source
        then pure ()
        else Nothing
      dependencies <- queryDependencies tableEnvironment source
      let queryKeys = concatMap queryDependencyKeys dependencies
          covered = Set.unions
            [ freePaths (queryKeyExpression key)
            | key <- queryKeys
            ]
          purePaths = Set.toAscList (Set.difference (freePaths source) covered)
      pureKeys <- traverse (urlifyFreePath environment source) purePaths
      if acceptsHeuristic heuristic dependencies queryKeys purePaths
        then Just (typ, map queryKeyExpression queryKeys <> pureKeys, dependencies)
        else Nothing
    descend = do
      rebuiltValue <- case locatedValue source of
        M.ECon kind constructor payload ->
          M.ECon kind constructor <$> traverse (recurse environment Nothing) payload
        M.ESome typ value -> M.ESome typ <$> recurse environment (Just typ) value
        M.EFfiApp moduleName name staticArguments arguments ->
          M.EFfiApp moduleName name staticArguments
            <$> traverse (\(value, typ) -> (,typ) <$> recurse environment (Just typ) value) arguments
        M.EApp function argument -> M.EApp
          <$> recurse environment Nothing function <*> recurse environment Nothing argument
        M.EAbs name domain range body -> M.EAbs name domain range
          <$> recurse (domain : environment) (Just range) body
        M.EStaticApp function argument ->
          M.EStaticApp <$> recurse environment Nothing function <*> pure argument
        M.EUnop operator value -> M.EUnop operator <$> recurse environment inferred value
        M.EBinop intness operator left right -> M.EBinop intness operator
          <$> recurse environment inferred left <*> recurse environment inferred right
        M.ERecord fields -> M.ERecord
          <$> traverse (\(name, value, typ) ->
            (name,,typ) <$> recurse environment (Just typ) value) fields
        M.EField record name -> M.EField <$> recurse environment Nothing record <*> pure name
        M.ERecordConcat left right -> M.ERecordConcat
          <$> recurse environment Nothing left <*> recurse environment Nothing right
        M.ERecordCut record names ->
          M.ERecordCut <$> recurse environment Nothing record <*> pure names
        M.ECase scrutinee branches input result -> M.ECase
          <$> recurse environment (Just input) scrutinee
          <*> traverse (\(pattern', body) -> (pattern',) <$>
            recurse (patternTypes pattern' <> environment) (Just result) body) branches
          <*> pure input <*> pure result
        M.EStrcat left right -> M.EStrcat
          <$> recurse environment inferred left <*> recurse environment inferred right
        M.EError value typ -> M.EError <$> recurse environment Nothing value <*> pure typ
        M.EReturnBlob content mime typ -> M.EReturnBlob
          <$> traverse (recurse environment Nothing) content
          <*> recurse environment Nothing mime <*> pure typ
        M.ERedirect value typ ->
          M.ERedirect <$> recurse environment Nothing value <*> pure typ
        M.EWrite value -> M.EWrite <$> recurse environment Nothing value
        M.ESeq first second -> M.ESeq
          <$> recurse environment Nothing first <*> recurse environment inferred second
        M.ELet name typ value body -> M.ELet name typ
          <$> recurse environment (Just typ) value
          <*> recurse (typ : environment) inferred body
        M.EClosure identifier captures ->
          M.EClosure identifier <$> traverse (recurse environment Nothing) captures
        M.EQuery {} -> pure (locatedValue source)
        M.EDml value failure ->
          M.EDml <$> recurse environment Nothing value <*> pure failure
        M.ENextval value -> M.ENextval <$> recurse environment Nothing value
        M.ESetval sequence' value -> M.ESetval
          <$> recurse environment Nothing sequence' <*> recurse environment Nothing value
        M.EUnurlify value typ optional ->
          M.EUnurlify <$> recurse environment Nothing value <*> pure typ <*> pure optional
        M.EJavaScript mode value ->
          M.EJavaScript mode <$> recurse environment Nothing value
        M.ESignalReturn value -> M.ESignalReturn <$> recurse environment Nothing value
        M.ESignalBind signal continuation -> M.ESignalBind
          <$> recurse environment Nothing signal <*> recurse environment Nothing continuation
        M.ESignalSource value -> M.ESignalSource <$> recurse environment Nothing value
        M.EServerCall call typ effect failure -> M.EServerCall
          <$> recurse environment Nothing call <*> pure typ <*> pure effect <*> pure failure
        M.ERecv channel typ -> M.ERecv <$> recurse environment Nothing channel <*> pure typ
        M.ESleep value -> M.ESleep <$> recurse environment Nothing value
        M.ESpawn value -> M.ESpawn <$> recurse environment Nothing value
        M.ESqlCache index typ keys action -> M.ESqlCache index typ
          <$> traverse (recurse environment Nothing) keys
          <*> recurse environment (Just typ) action
        M.ESqlCacheFlush typ flushes action -> M.ESqlCacheFlush typ
          <$> traverse (traverseFlush (recurse environment Nothing)) flushes
          <*> recurse environment (Just typ) action
        leaf -> pure leaf
      pure source {locatedValue = rebuiltValue}

registerCache
  :: M.Type
  -> [M.Expr]
  -> [QueryDependency]
  -> M.Expr
  -> State QueryState M.Expr
registerCache typ keys dependencies action = do
  state <- get
  let index = queryNextIndex state
      queryFields = concatMap (map queryKeyField . queryDependencyKeys) dependencies
      pureFieldCount = length keys - length queryFields
      site = CacheSite index
        (nubBy (==) (concatMap queryDependencyTables dependencies))
        (queryFields <> replicate pureFieldCount Nothing)
  modify' (\current -> current
    { queryNextIndex = index + 1
    , querySites = site : querySites current
    })
  pure (Located (locatedSpan action) (M.ESqlCache index typ keys action))

functionType :: M.Type -> Bool
functionType typ = case locatedValue typ of
  M.TFun {} -> True
  _ -> False

worthCaching :: M.Expr -> Bool
worthCaching expression = isQueryExpression expression || expressionSize expression > 5

expressionSize :: M.Expr -> Int
expressionSize expression = 1 + sum (map expressionSize (expressionChildren expression))

acceptsHeuristic
  :: SqlCacheHeuristic
  -> [QueryDependency]
  -> [QueryKey]
  -> [FreePath]
  -> Bool
acceptsHeuristic heuristic dependencies queryKeys purePaths = case heuristic of
  Smart -> null purePaths && comparableQueryArguments dependencies
  Always -> True
  Never -> length dependencies == 1 && null purePaths
  NoPureAll -> not (null dependencies)
  NoPureOne -> not (null dependencies) && null purePaths
  NoCombo -> null purePaths || null queryKeys

comparableQueryArguments :: [QueryDependency] -> Bool
comparableQueryArguments [] = False
comparableQueryArguments (first : rest) = go (keySet first) rest
  where
    keySet = Set.fromList . mapMaybeIdentities . queryDependencyKeys
    mapMaybeIdentities = foldr (\key found -> case
      sqlInjectionIdentity (queryKeyExpression key) of
        Just identity -> identity : found
        Nothing -> found) []
    go _ [] = True
    go accumulated (dependency : dependencies) =
      let next = keySet dependency
          union = Set.union accumulated next
       in (Set.size accumulated == Set.size union || Set.size next == Set.size union)
          && go union dependencies

queryDependencies :: TableEnvironment -> M.Expr -> Maybe [QueryDependency]
queryDependencies tableEnvironment = scan 0
  where
    scan depth expression = case queryOperand expression of
      Just (query, body, initial)
        | safeExpression body && safeExpression initial -> do
            keys <- traverse (shiftQueryKey depth) (analyzeQuery tableEnvironment query)
            pure [QueryDependency keys (queryTables tableEnvironment query)]
        | otherwise -> Nothing
      Nothing -> fmap concat (traverse
        (\(extra, child) -> scan (depth + extra) child)
        (expressionChildrenWithBinders expression))

queryOperand :: M.Expr -> Maybe (M.Expr, M.Expr, M.Expr)
queryOperand expression = case locatedValue expression of
  M.EQuery _ _ _ query body initial -> Just (query, body, initial)
  _ -> case collectApplications expression of
    (headExpression, [query, body, initial])
      | Just _ <- queryStateType headExpression -> Just (query, body, initial)
    _ -> Nothing

isQueryExpression :: M.Expr -> Bool
isQueryExpression expression = case queryOperand expression of
  Just _ -> True
  Nothing -> False

queryExpressionType :: M.Expr -> Maybe M.Type
queryExpressionType expression = case locatedValue expression of
  M.EQuery _ _ state _ _ _ -> Just state
  _ -> case collectApplications expression of
    (headExpression, [_, _, _]) -> queryStateType headExpression
    _ -> Nothing

shiftQueryKey :: Int -> QueryKey -> Maybe QueryKey
shiftQueryKey amount key = do
  expression <- shiftExpressionOut amount (queryKeyExpression key)
  pure key {queryKeyExpression = expression}

-- | Move an expression across @amount@ surrounding binders.  A reference to
-- one of those binders makes the move invalid; references under binders inside
-- the expression itself remain untouched.
shiftExpressionOut :: Int -> M.Expr -> Maybe M.Expr
shiftExpressionOut amount = walk 0
  where
    walk bound expression = do
      value <- case locatedValue expression of
        M.ERel index
          | index < bound -> Just (M.ERel index)
          | index < bound + amount -> Nothing
          | otherwise -> Just (M.ERel (index - amount))
        M.ECon kind constructor payload ->
          M.ECon kind constructor <$> traverse (walk bound) payload
        M.ESome typ value -> M.ESome typ <$> walk bound value
        M.EFfiApp moduleName name staticArguments arguments ->
          M.EFfiApp moduleName name staticArguments
            <$> traverse (\(value, typ) -> (,typ) <$> walk bound value) arguments
        M.EApp function argument -> M.EApp <$> walk bound function <*> walk bound argument
        M.EAbs name domain range body -> M.EAbs name domain range <$> walk (bound + 1) body
        M.EStaticApp function argument -> M.EStaticApp <$> walk bound function <*> pure argument
        M.EUnop operator value -> M.EUnop operator <$> walk bound value
        M.EBinop intness operator left right ->
          M.EBinop intness operator <$> walk bound left <*> walk bound right
        M.ERecord fields -> M.ERecord <$> traverse
          (\(name, value, typ) -> (name,,typ) <$> walk bound value) fields
        M.EField record name -> M.EField <$> walk bound record <*> pure name
        M.ERecordConcat left right -> M.ERecordConcat <$> walk bound left <*> walk bound right
        M.ERecordCut record names -> M.ERecordCut <$> walk bound record <*> pure names
        M.ECase scrutinee branches input result -> M.ECase
          <$> walk bound scrutinee
          <*> traverse (\(pattern', body) -> (pattern',) <$>
            walk (bound + length (patternTypes pattern')) body) branches
          <*> pure input <*> pure result
        M.EStrcat left right -> M.EStrcat <$> walk bound left <*> walk bound right
        M.EError message typ -> M.EError <$> walk bound message <*> pure typ
        M.EReturnBlob content mime typ -> M.EReturnBlob
          <$> traverse (walk bound) content <*> walk bound mime <*> pure typ
        M.ERedirect value typ -> M.ERedirect <$> walk bound value <*> pure typ
        M.EWrite value -> M.EWrite <$> walk bound value
        M.ESeq first second -> M.ESeq <$> walk bound first <*> walk bound second
        M.ELet name typ value body ->
          M.ELet name typ <$> walk bound value <*> walk (bound + 1) body
        M.EClosure identifier captures -> M.EClosure identifier <$> traverse (walk bound) captures
        M.EQuery fields nested state query body initial -> M.EQuery fields nested state
          <$> walk bound query <*> walk (bound + 2) body <*> walk bound initial
        M.EDml value failure -> M.EDml <$> walk bound value <*> pure failure
        M.ENextval value -> M.ENextval <$> walk bound value
        M.ESetval sequence' value -> M.ESetval <$> walk bound sequence' <*> walk bound value
        M.EUnurlify value typ optional ->
          M.EUnurlify <$> walk bound value <*> pure typ <*> pure optional
        M.EJavaScript mode value -> M.EJavaScript mode <$> walk bound value
        M.ESignalReturn value -> M.ESignalReturn <$> walk bound value
        M.ESignalBind signal continuation ->
          M.ESignalBind <$> walk bound signal <*> walk bound continuation
        M.ESignalSource value -> M.ESignalSource <$> walk bound value
        M.EServerCall call typ effect failure ->
          M.EServerCall <$> walk bound call <*> pure typ <*> pure effect <*> pure failure
        M.ERecv channel typ -> M.ERecv <$> walk bound channel <*> pure typ
        M.ESleep value -> M.ESleep <$> walk bound value
        M.ESpawn value -> M.ESpawn <$> walk bound value
        M.ESqlCache index typ keys action ->
          M.ESqlCache index typ <$> traverse (walk bound) keys <*> walk bound action
        M.ESqlCacheFlush typ flushes action -> M.ESqlCacheFlush typ
          <$> traverse (traverseFlush (walk bound)) flushes <*> walk bound action
        leaf -> Just leaf
      pure expression {locatedValue = value}

freePaths :: M.Expr -> Set.Set FreePath
freePaths = walk 0
  where
    walk bound expression = case expressionPath expression of
      Just (index, fields)
        | index >= bound -> Set.singleton (FreePath (index - bound) fields)
        | otherwise -> Set.empty
      Nothing -> Set.unions
        [ walk (bound + extra) child
        | (extra, child) <- expressionChildrenWithBinders expression
        ]

expressionChildrenWithBinders :: M.Expr -> [(Int, M.Expr)]
expressionChildrenWithBinders expression = case locatedValue expression of
  M.EAbs _ _ _ body -> [(1, body)]
  M.ELet _ _ value body -> [(0, value), (1, body)]
  M.ECase scrutinee branches _ _ ->
    (0, scrutinee) :
      [ (length (patternTypes pattern'), body)
      | (pattern', body) <- branches
      ]
  M.EQuery _ _ _ query body initial -> [(0, query), (2, body), (0, initial)]
  _ -> map (0,) (expressionChildren expression)

patternTypes :: M.Pattern -> [M.Type]
patternTypes pattern' = case locatedValue pattern' of
  M.PVar _ typ -> [typ]
  M.PPrim _ -> []
  M.PCon _ _ nested -> maybe [] patternTypes nested
  M.PRecord fields -> concatMap (patternTypes . second) fields
  M.PNone _ -> []
  M.PSome _ nested -> patternTypes nested
  where
    second (_, value, _) = value

urlifyFreePath :: [M.Type] -> M.Expr -> FreePath -> Maybe M.Expr
urlifyFreePath environment source (FreePath index fields) = do
  rootType <- atMay environment index
  typ <- foldl projectType (Just rootType) fields
  let location = locatedSpan source
      root = Located location (M.ERel index)
      value = foldl (\record field -> Located location
        (M.EField record (M.StaticName field))) root fields
      stringLiteral = Located location . M.EPrim . PrimString NormalString . ByteString.pack
      primitive name = Just (Located location
        (M.EFfiApp "Basis" name [] [(value, typ)]))
  case locatedValue typ of
    M.TFfi "Basis" name
      | name `elem` ["string", "url", "css_class", "id", "queryString"] ->
          primitive "urlifyString"
      | name == "int" -> primitive "urlifyInt"
      | name == "float" -> primitive "urlifyFloat"
      | name == "bool" -> primitive "urlifyBool"
      | name == "char" -> primitive "urlifyChar"
      | name == "time" -> primitive "urlifyTime"
      | name == "unit" -> Just (stringLiteral "")
    M.TRecord [] -> Just (stringLiteral "")
    _ -> Nothing
  where
    projectType current field = do
      typ <- current
      case locatedValue typ of
        M.TRecord fields' -> lookup field fields'
        _ -> Nothing

inferExpressionType
  :: Map.Map M.GlobalId M.Type
  -> [M.Type]
  -> M.Expr
  -> Maybe M.Type
inferExpressionType globals environment expression = case locatedValue expression of
  M.EPrim primitive -> Just (primitiveType expression primitive)
  M.ERel index -> atMay environment index
  M.ENamed identifier -> Map.lookup identifier globals
  M.ENone typ -> Just (Located (locatedSpan expression) (M.TOption typ))
  M.ESome typ _ -> Just (Located (locatedSpan expression) (M.TOption typ))
  M.EApp function _ -> do
    functionType' <- inferExpressionType globals environment function
    case locatedValue functionType' of
      M.TFun _ result -> Just result
      _ -> Nothing
  M.EAbs _ domain range _ -> Just (Located (locatedSpan expression) (M.TFun domain range))
  M.EStaticApp function _ -> inferExpressionType globals environment function
  M.EUnop _ value -> inferExpressionType globals environment value
  M.EBinop _ _ left _ -> inferExpressionType globals environment left
  M.ERecord fields -> Just (Located (locatedSpan expression)
    (M.TRecord [(name, typ) | (M.StaticName name, _, typ) <- fields]))
  M.EField record (M.StaticName field) -> do
    recordType <- inferExpressionType globals environment record
    case locatedValue recordType of
      M.TRecord fields -> lookup field fields
      _ -> Nothing
  M.ERecordConcat left right -> do
    leftType <- inferExpressionType globals environment left
    rightType <- inferExpressionType globals environment right
    case (locatedValue leftType, locatedValue rightType) of
      (M.TRecord leftFields, M.TRecord rightFields) ->
        Just (Located (locatedSpan expression) (M.TRecord (leftFields <> rightFields)))
      _ -> Nothing
  M.ECase _ _ _ result -> Just result
  M.EStrcat {} -> Just (basisType expression "string")
  M.EError _ typ -> Just typ
  M.EReturnBlob _ _ typ -> Just typ
  M.ERedirect _ typ -> Just typ
  M.EWrite _ -> Just (unitType expression)
  M.ESeq _ second -> inferExpressionType globals environment second
  M.ELet _ typ _ body -> inferExpressionType globals (typ : environment) body
  M.EQuery _ _ state _ _ _ -> Just state
  M.EDml {} -> Just (unitType expression)
  M.ENextval _ -> Just (basisType expression "int")
  M.ESetval {} -> Just (unitType expression)
  M.EUnurlify _ typ _ -> Just typ
  M.EJavaScript {} -> Just (basisType expression "string")
  M.ESignalReturn value -> inferExpressionType globals environment value
  M.ERecv _ typ -> Just typ
  M.ESleep _ -> Just (unitType expression)
  M.ESpawn _ -> Just (unitType expression)
  M.ESqlCache _ typ _ _ -> Just typ
  M.ESqlCacheFlush typ _ _ -> Just typ
  _ -> Nothing

primitiveType :: M.Expr -> Primitive -> M.Type
primitiveType source primitive = basisType source $ case primitive of
  PrimInt _ -> "int"
  PrimFloat _ -> "float"
  PrimString {} -> "string"
  PrimChar _ -> "char"

basisType :: M.Expr -> String -> M.Type
basisType source name = Located (locatedSpan source) (M.TFfi "Basis" name)

unitType :: M.Expr -> M.Type
unitType source = Located (locatedSpan source) (M.TRecord [])

atMay :: [value] -> Int -> Maybe value
atMay values index
  | index < 0 = Nothing
  | otherwise = case drop index values of
      value : _ -> Just value
      [] -> Nothing

traverseFlush
  :: Monad monad
  => (M.Expr -> monad M.Expr)
  -> M.SqlCacheFlush
  -> monad M.SqlCacheFlush
traverseFlush recurse flush = do
  keys <- traverse (traverse recurse) (M.sqlCacheFlushKeys flush)
  pure flush {M.sqlCacheFlushKeys = keys}

queryStateType :: M.Expr -> Maybe M.Type
queryStateType expression = case locatedValue expression of
  M.EFfi "Basis" "query" arguments -> stateArgument arguments
  M.EFfiApp "Basis" "query" arguments [] -> stateArgument arguments
  _ -> Nothing
  where
    stateArgument (_ : _ : argument : _) = staticType argument
    stateArgument _ = Nothing

collectApplications :: M.Expr -> (M.Expr, [M.Expr])
collectApplications = go []
  where
    go arguments expression = case locatedValue expression of
      M.EApp function argument -> go (argument : arguments) function
      _ -> (expression, arguments)

staticType :: M.StaticArg -> Maybe M.Type
staticType (M.StaticType typ) = Just typ
staticType (M.StaticFfi "Basis" "option" [element]) =
  Located (staticSpan element) . M.TOption <$> staticType element
staticType (M.StaticFfi "Basis" "list" [element]) =
  Located (staticSpan element) . M.TList <$> staticType element
staticType (M.StaticFfi moduleName name _) =
  Just (Located (staticSpanFallback moduleName name) (M.TFfi moduleName name))
staticType _ = Nothing

-- Static arguments carry no independent source location.  Types reconstructed
-- here are used only by code generation and inherit the enclosing expression's
-- location in normal lowering.  The zero-width sentinel is never user-facing.
staticSpan :: M.StaticArg -> Span
staticSpan _ = staticSpanFallback "" ""

staticSpanFallback :: String -> String -> Span
staticSpanFallback _ _ = Span "<sqlcache>" (SourcePos 1 1 0) (SourcePos 1 1 0)

cacheableType
  :: Map.Map M.GlobalId [(String, M.GlobalId, Maybe M.Type)]
  -> M.Type
  -> Bool
cacheableType datatypes = go []
  where
    go seen typ = case locatedValue typ of
      M.TFfi "Basis" name -> name `elem`
        ["unit", "int", "float", "bool", "char", "time", "string", "url", "css_class", "id", "queryString"]
      M.TRecord fields -> all (go seen . snd) fields
      M.TOption element -> go seen element
      M.TList element -> go seen element
      M.TDatatype identifier
        | identifier `elem` seen -> True
        | otherwise -> case Map.lookup identifier datatypes of
            Nothing -> False
            Just alternatives -> all (maybe True (go (identifier : seen)) . third) alternatives
      _ -> False
    third (_, _, value) = value

safeExpression :: M.Expr -> Bool
safeExpression expression
  | Just (query, body, initial) <- queryOperand expression =
      safeSqlExpression query && safeExpression body && safeExpression initial
  | otherwise = case locatedValue expression of
  M.EFfi moduleName name _ -> safeFfi moduleName name
  M.EFfiApp moduleName name _ arguments ->
    safeFfi moduleName name && all (safeExpression . fst) arguments
  M.ENamed _ -> False
  M.EClosure _ _ -> False
  M.EError _ _ -> False
  M.EReturnBlob {} -> False
  M.ERedirect {} -> False
  M.EDml {} -> False
  M.ENextval {} -> False
  M.ESetval {} -> False
  M.EJavaScript {} -> False
  M.ESignalReturn {} -> False
  M.ESignalBind {} -> False
  M.ESignalSource {} -> False
  M.EServerCall {} -> False
  M.ERecv {} -> False
  M.ESleep {} -> False
  M.ESpawn {} -> False
  M.ESqlCacheFlush {} -> False
  _ -> all safeExpression (expressionChildren expression)
  where
    safeFfi "Sqlcache" _ = False
    safeFfi "Basis" name = name `notElem`
      [ "channel", "send", "recv", "sleep", "spawn", "dml", "tryDml"
      , "nextval", "setval", "setCookie", "clearCookie", "setHeader"
      , "redirect", "returnBlob", "error", "debug", "rand", "now"
      -- Ur/Web's monomorphizer renders a page-body opening through
      -- get_settings/maybe_onload/maybe_onunload.  Fuse represents the same
      -- boundary with this internal helper, so treating it as a pure string
      -- constructor would incorrectly cache the request-specific page setup.
      , "__vr_tag_open"
      ]
    safeFfi _ _ = False

safeSqlExpression :: M.Expr -> Bool
safeSqlExpression expression = case locatedValue expression of
  M.ENamed _ -> True
  M.EFfi moduleName _ _ -> moduleName == "Basis"
  M.EFfiApp moduleName _ _ arguments ->
    moduleName == "Basis" && all (safeSqlExpression . fst) arguments
  _ -> all safeSqlExpression (expressionChildren expression)

flushDeclaration :: [CacheSite] -> TableEnvironment -> M.Decl -> M.Decl
flushDeclaration sites tableEnvironment declaration = declaration {locatedValue = case locatedValue declaration of
  M.DVal name identifier typ expression path ->
    M.DVal name identifier typ (flushExpression sites tableEnvironment expression) path
  M.DValRec bindings -> M.DValRec
    [ (name, identifier, typ, flushExpression sites tableEnvironment expression, path)
    | (name, identifier, typ, expression, path) <- bindings
    ]
  M.DTable name fields primary constraints -> M.DTable name fields
    (flushExpression sites tableEnvironment primary) (flushExpression sites tableEnvironment constraints)
  M.DView name fields query -> M.DView name fields (flushExpression sites tableEnvironment query)
  M.DIndexDynamic table modes -> M.DIndexDynamic
    (flushExpression sites tableEnvironment table) (flushExpression sites tableEnvironment modes)
  M.DTask schedule body -> M.DTask
    (flushExpression sites tableEnvironment schedule) (flushExpression sites tableEnvironment body)
  M.DPolicy policy -> M.DPolicy (case policy of
    M.PolicyClient expression -> M.PolicyClient (recurse expression)
    M.PolicyInsert expression -> M.PolicyInsert (recurse expression)
    M.PolicyDelete expression -> M.PolicyDelete (recurse expression)
    M.PolicyUpdate expression -> M.PolicyUpdate (recurse expression)
    M.PolicySequence expression -> M.PolicySequence (recurse expression))
  M.DPolicyRaw expression -> M.DPolicyRaw (recurse expression)
  other -> other}
  where
    recurse = flushExpression sites tableEnvironment

flushExpression :: [CacheSite] -> TableEnvironment -> M.Expr -> M.Expr
flushExpression sites tableEnvironment source = wrapDml sites tableEnvironment rebuilt
  where
    recurse = flushExpression sites tableEnvironment
    rebuilt = source {locatedValue = case locatedValue source of
      M.ECon kind constructor payload -> M.ECon kind constructor (recurse <$> payload)
      M.ESome typ value -> M.ESome typ (recurse value)
      M.EFfiApp moduleName name staticArguments arguments ->
        M.EFfiApp moduleName name staticArguments [(recurse value, typ) | (value, typ) <- arguments]
      M.EApp function argument -> M.EApp (recurse function) (recurse argument)
      M.EAbs name domain range body -> M.EAbs name domain range (recurse body)
      M.EStaticApp function argument -> M.EStaticApp (recurse function) argument
      M.EUnop operator value -> M.EUnop operator (recurse value)
      M.EBinop intness operator left right -> M.EBinop intness operator (recurse left) (recurse right)
      M.ERecord fields -> M.ERecord [(name, recurse value, typ) | (name, value, typ) <- fields]
      M.EField record name -> M.EField (recurse record) name
      M.ERecordConcat left right -> M.ERecordConcat (recurse left) (recurse right)
      M.ERecordCut record names -> M.ERecordCut (recurse record) names
      M.ECase scrutinee branches input result -> M.ECase (recurse scrutinee)
        [(pattern', recurse body) | (pattern', body) <- branches] input result
      M.EStrcat left right -> M.EStrcat (recurse left) (recurse right)
      M.EError value typ -> M.EError (recurse value) typ
      M.EReturnBlob content mime typ -> M.EReturnBlob (recurse <$> content) (recurse mime) typ
      M.ERedirect value typ -> M.ERedirect (recurse value) typ
      M.EWrite value -> M.EWrite (recurse value)
      M.ESeq first second -> M.ESeq (recurse first) (recurse second)
      M.ELet name typ value body -> M.ELet name typ (recurse value) (recurse body)
      M.EClosure identifier captures -> M.EClosure identifier (map recurse captures)
      M.EQuery fields nested state query body initial ->
        M.EQuery fields nested state (recurse query) (recurse body) (recurse initial)
      M.EDml value failure -> M.EDml (recurse value) failure
      M.ENextval value -> M.ENextval (recurse value)
      M.ESetval sequence' value -> M.ESetval (recurse sequence') (recurse value)
      M.EUnurlify value typ optional -> M.EUnurlify (recurse value) typ optional
      M.EJavaScript mode value -> M.EJavaScript mode (recurse value)
      M.ESignalReturn value -> M.ESignalReturn (recurse value)
      M.ESignalBind signal continuation -> M.ESignalBind (recurse signal) (recurse continuation)
      M.ESignalSource value -> M.ESignalSource (recurse value)
      M.EServerCall call typ effect failure -> M.EServerCall (recurse call) typ effect failure
      M.ERecv channel typ -> M.ERecv (recurse channel) typ
      M.ESleep value -> M.ESleep (recurse value)
      M.ESpawn value -> M.ESpawn (recurse value)
      M.ESqlCache index typ keys action -> M.ESqlCache index typ (map recurse keys) (recurse action)
      M.ESqlCacheFlush typ flushes action -> M.ESqlCacheFlush typ
        [flush {M.sqlCacheFlushKeys = map (fmap recurse) (M.sqlCacheFlushKeys flush)} | flush <- flushes]
        (recurse action)
      leaf -> leaf}

wrapDml :: [CacheSite] -> TableEnvironment -> M.Expr -> M.Expr
wrapDml sites tableEnvironment source = case dmlCommand source of
  Nothing -> source
  Just (command, resultType) ->
    let analysis = analyzeDml tableEnvironment command
        affects site = case dmlAnalysisTable analysis of
          Nothing -> True
          Just table -> null (cacheSiteTables site) || table `elem` cacheSiteTables site
        flushes = concat
          [ siteFlushes site analysis
          | site <- sites, affects site
          ]
     in if null flushes then source
          else source {locatedValue = M.ESqlCacheFlush resultType flushes source}

-- | Recover the dynamic SQL fragments that Ur/Web itself uses as cache keys.
-- A @Basis.sql_inject encoder value@ expression already has type string and
-- produces exactly the database literal used in the generated query, so it is
-- both stable across the two server backends and directly comparable with the
-- corresponding fragment in a DML predicate.
analyzeQuery :: TableEnvironment -> M.Expr -> [QueryKey]
analyzeQuery tableEnvironment query =
  [ QueryKey injection (Map.lookup identity equalities)
  | (identity, injection) <- uniqueSqlInjections query
  ]
  where
    aliases = queryAliases tableEnvironment query
    equalities = Map.fromList
      [ (identity, field)
      | predicate <- queryPredicates query
      , (field, value) <- predicateEqualities aliases predicate
      , Just identity <- [sqlInjectionIdentity value]
      ]

queryTables :: TableEnvironment -> M.Expr -> [String]
queryTables tableEnvironment query = case Map.elems (queryAliases tableEnvironment query) of
  [] -> tablesInExpression (tableEnvironmentNames tableEnvironment) query
  names -> nubBy (==) names

-- | The identity Ur/Web gives a SQL argument after its SQL simplification
-- pass: a De Bruijn variable, optionally followed by record projections.  Vr
-- recognizes that source shape before rendering the SQL builder to a string.
data SqlInjectionIdentity = SqlInjectionIdentity !Int ![String]
  deriving stock (Eq, Ord, Show)

uniqueSqlInjections :: M.Expr -> [(SqlInjectionIdentity, M.Expr)]
uniqueSqlInjections = nubBy sameIdentity . mapMaybeInjection . sqlInjections
  where
    mapMaybeInjection = foldr (\expression rest -> case sqlInjectionIdentity expression of
      Just identity -> (identity, expression) : rest
      Nothing -> rest) []
    sameIdentity (left, _) (right, _) = left == right

sqlInjections :: M.Expr -> [M.Expr]
sqlInjections expression
  | Just _ <- sqlInjectionIdentity expression = [expression]
  | otherwise = concatMap sqlInjections (expressionChildren expression)

sqlInjectionIdentity :: M.Expr -> Maybe SqlInjectionIdentity
sqlInjectionIdentity expression = do
  (_, arguments) <- basisApplication "sql_inject" expression
  value <- case reverse arguments of
    injected : _encoder : _ -> Just injected
    _ -> Nothing
  (index, fields) <- expressionPath value
  pure (SqlInjectionIdentity index fields)

expressionPath :: M.Expr -> Maybe (Int, [String])
expressionPath = go []
  where
    go fields expression = case locatedValue expression of
      M.ERel index -> Just (index, fields)
      M.EField record (M.StaticName field) -> go (field : fields) record
      _ -> Nothing

queryAliases :: TableEnvironment -> M.Expr -> Map.Map String String
queryAliases tableEnvironment = Map.fromList . foldExpression collect
  where
    collect expression = case basisApplication "sql_from_table" expression of
      Just (staticArguments, arguments)
        | table : _ <- reverse arguments
        , Just tableName <- resolveTable tableEnvironment table
        , alias : _ <- reverse [name | M.StaticName name <- staticArguments] ->
            [(alias, tableName)]
      _ -> []

queryPredicates :: M.Expr -> [M.Expr]
queryPredicates = foldExpression collect
  where
    collect expression = case basisApplication "sql_query1" expression of
      Just (_, [record]) ->
        [ value
        | name <- ["Where", "Having"]
        , Just value <- [recordField name record]
        ]
      _ -> []

recordField :: String -> M.Expr -> Maybe M.Expr
recordField wanted expression = case locatedValue expression of
  M.ERecord fields -> case
    [ value
    | (M.StaticName name, value, _) <- fields
    , name == wanted
    ] of
      value : _ -> Just value
      [] -> Nothing
  _ -> Nothing

predicateEqualities :: Map.Map String String -> M.Expr -> [(SqlField, M.Expr)]
predicateEqualities aliases expression = case sqlBinary expression of
  Just (operator, left, right)
    | operator == "sql_eq" ->
        fieldAndValue left right <> fieldAndValue right left
    | operator == "sql_and" ->
        predicateEqualities aliases left <> predicateEqualities aliases right
  _ -> []
  where
    fieldAndValue field value = case (sqlField aliases field, sqlInjectionIdentity value) of
      (Just field', Just _) -> [(field', value)]
      _ -> []

sqlBinary :: M.Expr -> Maybe (String, M.Expr, M.Expr)
sqlBinary expression = do
  (_, arguments) <- basisApplication "sql_binary" expression
  case reverse arguments of
    right : left : operator : _ -> do
      name <- basisHeadName operator
      pure (name, left, right)
    _ -> Nothing

sqlField :: Map.Map String String -> M.Expr -> Maybe SqlField
sqlField aliases expression = do
  (staticArguments, arguments) <- basisApplication "sql_field" expression
  if null arguments then pure () else Nothing
  case reverse [name | M.StaticName name <- staticArguments] of
    field : alias : _ -> SqlField <$> Map.lookup alias aliases <*> pure field
    _ -> Nothing

basisHeadName :: M.Expr -> Maybe String
basisHeadName expression = case applicationParts expression of
  Just ("Basis", name, _, []) -> Just name
  _ -> Nothing

basisApplication :: String -> M.Expr -> Maybe ([M.StaticArg], [M.Expr])
basisApplication wanted expression = case applicationParts expression of
  Just ("Basis", name, staticArguments, arguments)
    | name == wanted -> Just (staticArguments, arguments)
  _ -> Nothing

applicationParts :: M.Expr -> Maybe (String, String, [M.StaticArg], [M.Expr])
applicationParts = go [] []
  where
    go runtimeArguments extraStatic expression = case locatedValue expression of
      M.EApp function argument -> go (argument : runtimeArguments) extraStatic function
      M.EStaticApp function argument -> go runtimeArguments (argument : extraStatic) function
      M.EFfi moduleName name staticArguments ->
        Just (moduleName, name, staticArguments <> extraStatic, runtimeArguments)
      M.EFfiApp moduleName name staticArguments directArguments ->
        Just (moduleName, name, staticArguments <> extraStatic,
          map fst directArguments <> runtimeArguments)
      _ -> Nothing

foldExpression :: (M.Expr -> [value]) -> M.Expr -> [value]
foldExpression collect expression =
  collect expression <> concatMap (foldExpression collect) (expressionChildren expression)

resolveTable :: TableEnvironment -> M.Expr -> Maybe String
resolveTable tableEnvironment expression = case locatedValue expression of
  M.ENamed identifier -> Map.lookup identifier (tableEnvironmentGlobals tableEnvironment)
  M.EPrim (PrimString _ bytes) -> Just (ByteString.unpack bytes)
  _ -> Nothing

analyzeDml :: TableEnvironment -> M.Expr -> DmlAnalysis
analyzeDml tableEnvironment command = case applicationParts command of
  Just ("Basis", "update", _, arguments)
    | predicate : table : fields : _ <- reverse arguments ->
        let tableName = resolveTable tableEnvironment table
            aliases = maybe Map.empty (Map.singleton "T") tableName
            oldRows = predicateRows aliases predicate
            changed = maybe Map.empty
              (\name -> recordSqlValues (SqlField name) fields)
              tableName
            newRows = map (Map.union changed) oldRows
         in DmlAnalysis tableName (oldRows <> newRows)
  Just ("Basis", "delete", _, arguments)
    | predicate : table : _ <- reverse arguments ->
        let tableName = resolveTable tableEnvironment table
            aliases = maybe Map.empty (Map.singleton "T") tableName
         in DmlAnalysis tableName (predicateRows aliases predicate)
  Just ("Basis", "insert", _, arguments)
    | fields : table : _ <- reverse arguments ->
        let tableName = resolveTable tableEnvironment table
            rows = maybe [Map.empty] (\name -> [recordSqlValues (SqlField name) fields]) tableName
         in DmlAnalysis tableName rows
  _ -> DmlAnalysis Nothing [Map.empty]

recordSqlValues :: (String -> SqlField) -> M.Expr -> Map.Map SqlField M.Expr
recordSqlValues makeField expression = case locatedValue expression of
  M.ERecord fields -> Map.fromList
    [ (makeField name, value)
    | (M.StaticName name, value, _) <- fields
    ]
  _ -> Map.empty

-- | Produce one possible set of column values for each disjunct.  Unknown
-- predicates deliberately become an empty map, which later emits wildcard
-- keys.  That fallback may evict more entries, but can never retain stale
-- data.
predicateRows :: Map.Map String String -> M.Expr -> [Map.Map SqlField M.Expr]
predicateRows aliases expression = case sqlBinary expression of
  Just (operator, left, right)
    | operator == "sql_eq" -> case
        predicateEqualities aliases expression of
          [] -> [Map.empty]
          equalities -> [Map.fromList equalities]
    | operator == "sql_and" ->
        [ Map.union leftRow rightRow
        | leftRow <- predicateRows aliases left
        , rightRow <- predicateRows aliases right
        ]
    | operator == "sql_or" -> predicateRows aliases left <> predicateRows aliases right
  _ -> [Map.empty]

siteFlushes :: CacheSite -> DmlAnalysis -> [M.SqlCacheFlush]
siteFlushes site analysis =
  [ M.SqlCacheFlush (cacheSiteIndex site) pattern'
  | pattern' <- removeRedundantPatterns
      [ map (fieldValue row) (cacheSiteKeys site)
      | row <- case dmlAnalysisRows analysis of
          [] -> [Map.empty]
          rows -> rows
      ]
  ]
  where
    fieldValue _ Nothing = Nothing
    fieldValue row (Just field) = Map.lookup field row

removeRedundantPatterns :: [[Maybe M.Expr]] -> [[Maybe M.Expr]]
removeRedundantPatterns = foldr add []
  where
    add candidate existing
      | any (candidate `madeRedundantBy`) existing = existing
      | otherwise = candidate : filter (not . (`madeRedundantBy` candidate)) existing
    madeRedundantBy specific broad = and (zipWith matches specific broad)
      && length specific == length broad
    matches _ Nothing = True
    matches (Just left) (Just right) = left == right
    matches Nothing (Just _) = False

dmlCommand :: M.Expr -> Maybe (M.Expr, M.Type)
dmlCommand expression = case locatedValue expression of
  M.EDml command _ -> Just (command, unitResultType)
  _ -> case collectApplications expression of
    (headExpression, [command]) -> case locatedValue headExpression of
      M.EFfi "Basis" "dml" _ -> Just (command, unitResultType)
      M.EFfiApp "Basis" "dml" _ [] -> Just (command, unitResultType)
      M.EFfi "Basis" "tryDml" _ -> Just (command, optionStringType)
      M.EFfiApp "Basis" "tryDml" _ [] -> Just (command, optionStringType)
      _ -> Nothing
    _ -> Nothing
  where
    location = locatedSpan expression
    unitResultType = Located location (M.TRecord [])
    stringType = Located location (M.TFfi "Basis" "string")
    optionStringType = Located location (M.TOption stringType)

tablesInExpression :: [String] -> M.Expr -> [String]
tablesInExpression tables expression =
  [table | table <- tables, any (table `isInfixOf`) (expressionTexts expression)]

expressionTexts :: M.Expr -> [String]
expressionTexts expression = case locatedValue expression of
  M.EPrim (PrimString _ bytes) -> [ByteString.unpack bytes]
  _ -> concatMap expressionTexts (expressionChildren expression)

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
  M.EReturnBlob content mime _ -> maybe [] pure content <> [mime]
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
