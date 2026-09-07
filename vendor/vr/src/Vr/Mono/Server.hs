{-# LANGUAGE DerivingStrategies #-}

-- | The server-visible projection of combined Mono programs.
--
-- Ur/Web runs its side check only after browser programs have been extracted
-- and the remaining server program has been shaken.  Vr keeps both sides in
-- one Mono tree for its direct backends, so this module provides the shared
-- equivalent: identify definitions that belong exclusively to client islands
-- and reject a client-only foreign value if a server root still depends on it.
module Vr.Mono.Server
  ( ForeignName
  , ForeignConstructor (..)
  , collectForeignConstructors
  , serverForeignConstructors
  , clientOnlyDefinitionIds
  , clientOnlyForeignNames
  , foreignHtmlTagNames
  , serverForeignNames
  , serverReachableDefinitionIds
  , serverExpressionChildren
  , serverForeignProblems
  , serverSideProblems
  , integerHtmlArgument
  , stringHtmlArgument
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Vr.Mono.Syntax as M
import Vr.Project (ProjectDirective (..), ProjectPlan (..))
import Vr.Source
  ( Diagnostic
  , DiagnosticPhase (BackendPhase)
  , Located (..)
  , Span
  , diagnostic
  , noSpan
  )

type ForeignName = (String, String)

-- | One foreign-signature datatype constructor that survived into Mono.
-- IDs follow first occurrence order and are shared by LLVM helper symbols,
-- the direct-JavaScript runtime, and its generated N-API sidecar.
data ForeignConstructor = ForeignConstructor
  { foreignConstructorId :: !Int
  , foreignConstructorModule :: !String
  , foreignConstructorDatatype :: !String
  , foreignConstructorName :: !String
  , foreignConstructorKind :: !M.DatatypeKind
  , foreignConstructorPayload :: !(Maybe M.Type)
  }
  deriving stock (Eq, Show)

-- | Collect foreign datatype constructors from both expressions and case
-- patterns.  Mono has no standalone declaration for an FFI datatype, so the
-- constructors that remain observable are recovered from their resolved
-- 'PConFfi' nodes.
collectForeignConstructors :: M.File -> [ForeignConstructor]
collectForeignConstructors file = zipWith identify [0 ..] unique
  where
    occurrences = concatMap declarationConstructors (M.fileDeclarations file)
    unique = reverse (snd (foldl remember (Set.empty, []) occurrences))
    remember (seen, done) constructor
      | Set.member (key constructor) seen = (seen, done)
      | otherwise = (Set.insert (key constructor) seen, constructor : done)
    key (_, moduleName, datatypeName, constructorName, _) =
      (moduleName, datatypeName, constructorName)
    identify identifier (kind, moduleName, datatypeName, constructorName, payload) =
      ForeignConstructor identifier moduleName datatypeName constructorName kind payload

    declarationConstructors declaration =
      concatMap expressionConstructors (declarationAllExpressions declaration)
    declarationAllExpressions declaration = case locatedValue declaration of
      M.DVal _ _ _ expression _ -> [expression]
      M.DValRec bindings -> [expression | (_, _, _, expression, _) <- bindings]
      M.DTable _ _ primary constraints -> [primary, constraints]
      M.DView _ _ query -> [query]
      M.DIndexDynamic table modes -> [table, modes]
      M.DTask schedule body -> [schedule, body]
      M.DPolicy policy -> policyExpressions policy
      M.DPolicyRaw expression -> [expression]
      _ -> []
    expressionConstructors expression = direct <> patterns
      <> concatMap expressionConstructors (allExpressionChildren expression)
      where
        direct = case locatedValue expression of
          M.ECon kind (M.PConFfi moduleName datatypeName constructorName payload) _
            | moduleName /= "Basis" ->
                [(kind, moduleName, datatypeName, constructorName, payload)]
          _ -> []
        patterns = case locatedValue expression of
          M.ECase _ branches _ _ -> concatMap (patternConstructors . fst) branches
          _ -> []
    patternConstructors pattern' = direct <> case locatedValue pattern' of
      M.PCon _ _ nested -> maybe [] patternConstructors nested
      M.PRecord fields -> concatMap (patternConstructors . second) fields
      M.PSome _ nested -> patternConstructors nested
      _ -> []
      where
        direct = case locatedValue pattern' of
          M.PCon kind (M.PConFfi moduleName datatypeName constructorName payload) _
            | moduleName /= "Basis" ->
                [(kind, moduleName, datatypeName, constructorName, payload)]
          _ -> []
        second (_, value, _) = value
    allExpressionChildren expression = case locatedValue expression of
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
        [cachedKey | flush <- flushes, Just cachedKey <- M.sqlCacheFlushKeys flush] <> [action]
      _ -> []

-- | Foreign constructors evaluated by the server projection.  Constructor
-- IDs remain the IDs from the complete Mono file, so browser and server
-- metadata never disagree when a constructor occurs on both sides.
serverForeignConstructors :: ProjectPlan -> M.File -> [ForeignConstructor]
serverForeignConstructors plan file =
  filter (\constructor -> Set.member (constructorKey constructor) wanted) allConstructors
  where
    declarations = M.fileDeclarations file
    reachable = serverReachableDefinitionIds plan file
    roots = concatMap declarationRootExpressions declarations <>
      [ expression
      | declaration <- declarations
      , (identifier, expression) <- declarationDefinitions declaration
      , Set.member identifier reachable
      ]
    wanted = foldMap serverKeys roots
    allConstructors = collectForeignConstructors file
    constructorKey constructor =
      ( foreignConstructorModule constructor
      , foreignConstructorDatatype constructor
      , foreignConstructorName constructor
      )
    serverKeys expression = direct <> patterns
      <> foldMap serverKeys (serverExpressionChildren expression)
      where
        direct = case locatedValue expression of
          M.ECon _ (M.PConFfi moduleName datatypeName constructorName _) _
            | moduleName /= "Basis" -> Set.singleton (moduleName, datatypeName, constructorName)
          _ -> Set.empty
        patterns = case locatedValue expression of
          M.ECase _ branches _ _ -> foldMap (patternKeys . fst) branches
          _ -> Set.empty
    patternKeys pattern' = direct <> case locatedValue pattern' of
      M.PCon _ _ nested -> maybe Set.empty patternKeys nested
      M.PRecord fields -> foldMap (patternKeys . second) fields
      M.PSome _ nested -> patternKeys nested
      _ -> Set.empty
      where
        direct = case locatedValue pattern' of
          M.PCon _ (M.PConFfi moduleName datatypeName constructorName _) _
            | moduleName /= "Basis" -> Set.singleton (moduleName, datatypeName, constructorName)
          _ -> Set.empty
        second (_, value, _) = value
-- | Built-in and project-configured names that the pinned compiler rejects
-- when they remain in server code.  @serverOnly@ is intentionally absent:
-- the pinned compiler records that setting but never consults it.
clientOnlyForeignNames :: ProjectPlan -> Set.Set ForeignName
clientOnlyForeignNames plan = builtinClientOnly <> directiveNames "clientOnly" plan

-- | Definitions that do not survive the server-root reachability closure.
-- This is the set that a server backend may omit.  It includes both values
-- used exclusively from extracted browser islands and completely dead values.
clientOnlyDefinitionIds :: ProjectPlan -> [M.Decl] -> Set.Set M.GlobalId
clientOnlyDefinitionIds plan declarations =
  Set.difference allDefinitions (serverReachableDefinitionIds plan (M.File declarations []))
  where
    allDefinitions = Set.fromList
      [ identifier
      | declaration <- declarations
      , (identifier, _) <- declarationDefinitions declaration
      ]

-- | Diagnose client-only values that are still demanded by a server entry
-- point or server initialization expression.  Definitions reachable only
-- from extracted browser code are deliberately accepted.
serverSideProblems :: ProjectPlan -> M.File -> [Diagnostic]
serverSideProblems plan file = concatMap expressionProblems serverExpressions
  where
    declarations = M.fileDeclarations file
    names = clientOnlyForeignNames plan
    reachable = serverReachableDefinitionIds plan file
    serverExpressions = concatMap declarationRootExpressions declarations <>
      [ expression
      | declaration <- declarations
      , (identifier, expression) <- declarationDefinitions declaration
      , Set.member identifier reachable
      ]
    expressionProblems expression = directProblems expression <>
      concatMap expressionProblems (serverExpressionChildren expression)
    directProblems expression = case locatedValue expression of
      M.EFfi moduleName member _
        | Set.member (moduleName, member) names -> [clientForeign expression moduleName member]
      M.EFfiApp moduleName member _ _
        | Set.member (moduleName, member) names -> [clientForeign expression moduleName member]
      M.ESignalReturn {} -> [clientConstruct expression "signal return"]
      M.ESignalBind {} -> [clientConstruct expression "signal bind"]
      M.ESignalSource {} -> [clientConstruct expression "signal source"]
      M.EServerCall {} -> [clientConstruct expression "RPC call"]
      M.ERecv {} -> [clientConstruct expression "channel receive"]
      M.ESleep {} -> [clientConstruct expression "browser sleep"]
      M.ESpawn {} -> [clientConstruct expression "browser task spawn"]
      M.EJavaScript mode _ -> case mode of
        M.JavaScriptSource {} -> []
        M.JavaScriptAttribute -> [clientConstruct expression "JavaScript attribute"]
        M.JavaScriptScript -> [clientConstruct expression "JavaScript script"]
      _ -> []
    clientForeign expression moduleName member =
      diagnostic BackendPhase "server-client-only" (locatedSpan expression)
        ("Server-side code uses client-side-only identifier \""
          <> displayName moduleName member <> "\"")
    clientConstruct expression construct =
      diagnostic BackendPhase "server-client-only" (locatedSpan expression)
        ("Server-side code contains a client-side-only " <> construct)

-- | Direct JavaScript cannot silently reinterpret a custom server FFI as a
-- Basis intrinsic.  Report every server-visible use so that backend fails
-- closed until its native-addon bridge is available; browser-only uses have
-- already been extracted and are intentionally ignored here.
serverForeignProblems :: ProjectPlan -> M.File -> [Diagnostic]
serverForeignProblems plan file = map foreignProblem (Set.toAscList (serverForeignNames plan file))
  where
    foreignProblem (moduleName, member) =
      diagnostic BackendPhase "javascript-server-ffi" (foreignUseSpan plan file (moduleName, member))
        ("Direct JavaScript server execution of " <> moduleName <> "." <> member
          <> " requires a native FFI bridge")

-- | Definitions retained by the server projection.  Start with actual server
-- roots, then close through global references in expressions evaluated on the
-- server.  This is deliberately narrower than "all non-client definitions":
-- dead foreign calls must not force an otherwise unnecessary native symbol to
-- be linked into a direct-JavaScript application.
serverReachableDefinitionIds :: ProjectPlan -> M.File -> Set.Set M.GlobalId
serverReachableDefinitionIds _plan file = close initial
  where
    declarations = M.fileDeclarations file
    definitions = Map.fromList (concatMap declarationDefinitions declarations)
    initial = Set.fromList (concatMap declarationRootIds declarations)
      <> foldMap expressionGlobalIds (concatMap declarationRootExpressions declarations)
    close known =
      let referenced = foldMap expressionGlobalIds
            [ expression
            | identifier <- Set.toList known
            , Just expression <- [Map.lookup identifier definitions]
            ]
          next = known <> referenced
       in if next == known then known else close next

-- | Custom FFI values that survive the server-root reachability closure.
-- Browser event/source islands are excluded by 'serverExpressionChildren'.
serverForeignNames :: ProjectPlan -> M.File -> Set.Set ForeignName
serverForeignNames plan file =
  Set.difference (foldMap expressionForeignNames
    (concatMap declarationRootExpressions declarations <> reachableExpressions)
    ) (foreignHtmlTagNames file)
  where
    declarations = M.fileDeclarations file
    reachable = serverReachableDefinitionIds plan file
    reachableExpressions =
      [ expression
      | declaration <- declarations
      , (identifier, expression) <- declarationDefinitions declaration
      , Set.member identifier reachable
      ]

-- | Foreign declarations at one of Ur/Web's abstract tag constructor types
-- are HTML descriptor declarations, not C symbols to invoke.  The reference
-- backend uses their member names as literal element names.
foreignHtmlTagNames :: M.File -> Set.Set ForeignName
foreignHtmlTagNames file = Set.fromList
  [ (moduleName, member)
  | declaration <- M.fileDeclarations file
  , M.DForeign moduleName member typ <- [locatedValue declaration]
  , isHtmlTagType typ
  ]
  where
    isHtmlTagType typ = case locatedValue typ of
      M.TFfi "Basis" name -> name `elem`
        ["bodyTag", "bodyTagStandalone", "formTag", "cformTag"]
      _ -> False

declarationDefinitions :: M.Decl -> [(M.GlobalId, M.Expr)]
declarationDefinitions declaration = case locatedValue declaration of
  M.DVal _ identifier _ expression _ -> [(identifier, expression)]
  M.DValRec bindings -> [(identifier, expression) | (_, identifier, _, expression, _) <- bindings]
  _ -> []

declarationRootIds :: M.Decl -> [M.GlobalId]
declarationRootIds declaration = case locatedValue declaration of
  M.DExport _ _ identifier _ _ _ -> [identifier]
  M.DDatabase info -> [M.databaseExpunge info, M.databaseInitialize info]
  M.DOnError identifier -> [identifier]
  _ -> []

declarationRootExpressions :: M.Decl -> [M.Expr]
declarationRootExpressions declaration = case locatedValue declaration of
  M.DTask schedule body -> [schedule, body]
  M.DTable _ _ primary constraints -> [primary, constraints]
  M.DView _ _ query -> [query]
  M.DIndexDynamic table modes -> [table, modes]
  M.DPolicy policy -> policyExpressions policy
  M.DPolicyRaw expression -> [expression]
  _ -> []

policyExpressions :: M.Policy -> [M.Expr]
policyExpressions policy = case policy of
  M.PolicyClient expression -> [expression]
  M.PolicyInsert expression -> [expression]
  M.PolicyDelete expression -> [expression]
  M.PolicyUpdate expression -> [expression]
  M.PolicySequence expression -> [expression]

expressionGlobalIds :: M.Expr -> Set.Set M.GlobalId
expressionGlobalIds expression = direct <> foldMap expressionGlobalIds (serverExpressionChildren expression)
  where
    direct = case locatedValue expression of
      M.ENamed identifier -> Set.singleton identifier
      M.EClosure identifier _ -> Set.singleton identifier
      _ -> Set.empty

expressionForeignNames :: M.Expr -> Set.Set ForeignName
expressionForeignNames expression = direct <> foldMap expressionForeignNames (serverExpressionChildren expression)
  where
    direct = case locatedValue expression of
      M.EFfi moduleName member _ | moduleName /= "Basis" -> Set.singleton (moduleName, member)
      M.EFfiApp moduleName member _ _ | moduleName /= "Basis" -> Set.singleton (moduleName, member)
      _ -> Set.empty

foreignUseSpan :: ProjectPlan -> M.File -> ForeignName -> Span
foreignUseSpan plan file wanted = case
  [ locatedSpan foundExpression
  | expression <- concatMap declarationRootExpressions declarations <> reachableExpressions
  , (foundName, foundExpression) <- expressionForeignUses expression
  , foundName == wanted
  ] of
    location : _ -> location
    [] -> noSpan
  where
    declarations = M.fileDeclarations file
    reachable = serverReachableDefinitionIds plan file
    reachableExpressions =
      [ expression
      | declaration <- declarations
      , (identifier, expression) <- declarationDefinitions declaration
      , Set.member identifier reachable
      ]
    expressionForeignUses expression = case locatedValue expression of
      M.EFfi moduleName member _ | moduleName /= "Basis" -> [((moduleName, member), expression)]
      M.EFfiApp moduleName member _ _ | moduleName /= "Basis" -> [((moduleName, member), expression)]
      _ -> concatMap expressionForeignUses (serverExpressionChildren expression)

-- | Children evaluated by the server.  A tag descriptor is compile-time
-- metadata, while event fields in its attribute record are browser islands;
-- ordinary attributes, static markup, and JavaScript-source values remain
-- server work.
serverExpressionChildren :: M.Expr -> [M.Expr]
serverExpressionChildren expression
  | (function, [classes, _, style, _, attributes, _descriptor, child]) <- collectApplications expression
  , M.EFfi "Basis" "tag" _ <- locatedValue function =
      [classes, style] <> serverTagAttributeChildren attributes <> [child]
  | (function, [classes, _, style, _, attributes, _descriptor]) <- collectApplications expression
  , M.EFfi "Basis" "__vr_tag_open" _ <- locatedValue function =
      [classes, style] <> serverTagAttributeChildren attributes
  | otherwise = case locatedValue expression of
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
      M.EJavaScript mode value -> case mode of
        M.JavaScriptSource {} -> [value]
        _ -> []
      M.ERecv channel _ -> [channel]
      M.ESleep value -> [value]
      M.ESpawn value -> [value]
      M.ESqlCache _ _ keys action -> keys <> [action]
      M.ESqlCacheFlush _ flushes action ->
        [key | flush <- flushes, Just key <- M.sqlCacheFlushKeys flush] <> [action]
      _ -> []

-- Event handlers live in the attribute record of Basis.tag.  Restrict this
-- name-based projection to that operand; ordinary records may legitimately
-- contain server fields named Code, Signal, or On*.
serverTagAttributeChildren :: M.Expr -> [M.Expr]
serverTagAttributeChildren attributes = case locatedValue attributes of
  M.ERecord fields ->
    [ value
    | (name, value, _) <- fields
    , case name of
        M.StaticName field -> not (clientRootField field)
        _ -> True
    ]
  _ -> [attributes]

clientRootField :: String -> Bool
clientRootField name = take 2 name == "On" || name `elem` ["Signal", "Code"]

-- | The evaluated integer in an immediately displayed decimal string. Its
-- digits and optional minus sign need no HTML escaping. Backends may write
-- this value directly, preserving its evaluation point and page-limit checks.
integerHtmlArgument :: M.Expr -> Maybe M.Expr
integerHtmlArgument expression =
  stringHtmlArgument expression >>= unaryBasis "intToString"

-- | The string escaped by an immediate HTML write. The reference's direct
-- writer differs from its string-returning escaper for printable Unicode.
stringHtmlArgument :: M.Expr -> Maybe M.Expr
stringHtmlArgument = unaryBasis "htmlifyString"

unaryBasis :: String -> M.Expr -> Maybe M.Expr
unaryBasis wanted source = case collectApplications source of
  (function, [argument]) | M.EFfi "Basis" actual _ <- locatedValue function
    , actual == wanted -> Just argument
  (function, []) | M.EFfiApp "Basis" actual _ [(argument, _)] <- locatedValue function
    , actual == wanted -> Just argument
  _ -> Nothing

collectApplications :: M.Expr -> (M.Expr, [M.Expr])
collectApplications = go []
  where
    go arguments expression = case locatedValue expression of
      M.EApp function argument -> go (argument : arguments) function
      _ -> (expression, arguments)

directiveNames :: String -> ProjectPlan -> Set.Set ForeignName
directiveNames wanted plan = Set.fromList
  [ (moduleName, member)
  | directive <- projectDirectives plan
  , projectDirectiveName directive == wanted
  , let (moduleName, suffix) = break (== '.') (projectDirectiveArgument directive)
  , '.' : member <- [suffix]
  , not (null moduleName)
  , not (null member)
  ]

builtinClientOnly :: Set.Set ForeignName
builtinClientOnly = Set.fromList
  [("Basis", name) | name <-
    [ "get_client_source", "current", "alert", "confirm", "recv", "sleep", "spawn"
    , "onError", "onFail", "onConnectFail", "onDisconnect", "onServerError"
    , "mouseEvent", "keyEvent", "onClick", "onContextmenu", "onDblclick"
    , "onKeydown", "onKeypress", "onKeyup", "onMousedown", "onMouseenter"
    , "onMouseleave", "onMousemove", "onMouseout", "onMouseover", "onMouseup"
    , "preventDefault", "stopPropagation", "giveFocus"
    ]]

displayName :: String -> String -> String
displayName "Basis" "get_client_source" = "Basis.get"
displayName "" member = member
displayName moduleName member = moduleName <> "." <> member
