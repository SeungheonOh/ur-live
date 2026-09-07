-- | Ur/Web-compatible database blob file-cache instrumentation.
--
-- A cache-enabled query first asks the database for SHA-512 digests in place
-- of blob columns.  Missing files raise an unlimited retry and leave a flag
-- in the request context.  The retry executes the original query, stores its
-- blobs, and continues with the original row callback.  Later requests can
-- therefore avoid transferring the blob values from the database.
module Vr.Mono.FileCache
  ( instrumentFile
  ) where

import qualified Data.ByteString.Char8 as ByteString
import Data.Char (toLower)
import Data.List (intercalate, nub)
import qualified Vr.Mono.Syntax as M
import Vr.Source
  ( Located (..)
  , Primitive (PrimString)
  , Span
  , StringMode (NormalString)
  )

instrumentFile :: String -> M.File -> M.File
instrumentFile databaseSystem file = file
  { M.fileDeclarations = map instrumentDeclaration (M.fileDeclarations file)
  }
  where
    instrumentDeclaration declaration = declaration {locatedValue = case locatedValue declaration of
      M.DVal name identifier typ expression path ->
        M.DVal name identifier typ (instrumentExpression databaseSystem expression) path
      M.DValRec bindings -> M.DValRec
        [ (name, identifier, typ, instrumentExpression databaseSystem expression, path)
        | (name, identifier, typ, expression, path) <- bindings
        ]
      M.DTable name fields primary constraints -> M.DTable name fields
        (instrumentExpression databaseSystem primary)
        (instrumentExpression databaseSystem constraints)
      M.DView name fields query ->
        M.DView name fields (instrumentExpression databaseSystem query)
      M.DIndexDynamic table modes -> M.DIndexDynamic
        (instrumentExpression databaseSystem table)
        (instrumentExpression databaseSystem modes)
      M.DTask schedule body -> M.DTask
        (instrumentExpression databaseSystem schedule)
        (instrumentExpression databaseSystem body)
      M.DPolicy policy -> M.DPolicy (case policy of
        M.PolicyClient value -> M.PolicyClient (recurse value)
        M.PolicyInsert value -> M.PolicyInsert (recurse value)
        M.PolicyDelete value -> M.PolicyDelete (recurse value)
        M.PolicyUpdate value -> M.PolicyUpdate (recurse value)
        M.PolicySequence value -> M.PolicySequence (recurse value))
      M.DPolicyRaw expression -> M.DPolicyRaw (recurse expression)
      other -> other}
      where
        recurse = instrumentExpression databaseSystem

instrumentExpression :: String -> M.Expr -> M.Expr
instrumentExpression databaseSystem source = instrumentQuery databaseSystem rebuilt
  where
    recurse = instrumentExpression databaseSystem
    rebuilt = source {locatedValue = case locatedValue source of
      M.ECon kind constructor payload -> M.ECon kind constructor (recurse <$> payload)
      M.ESome typ value -> M.ESome typ (recurse value)
      M.EFfiApp moduleName name staticArguments arguments ->
        M.EFfiApp moduleName name staticArguments
          [(recurse value, typ) | (value, typ) <- arguments]
      M.EApp function argument -> M.EApp (recurse function) (recurse argument)
      M.EAbs name domain range body -> M.EAbs name domain range (recurse body)
      M.EStaticApp function argument -> M.EStaticApp (recurse function) argument
      M.EUnop operator value -> M.EUnop operator (recurse value)
      M.EBinop intness operator left right ->
        M.EBinop intness operator (recurse left) (recurse right)
      M.ERecord fields -> M.ERecord
        [(name, recurse value, typ) | (name, value, typ) <- fields]
      M.EField record fieldName -> M.EField (recurse record) fieldName
      M.ERecordConcat left right -> M.ERecordConcat (recurse left) (recurse right)
      M.ERecordCut record fields -> M.ERecordCut (recurse record) fields
      M.ECase scrutinee branches input result -> M.ECase
        (recurse scrutinee) [(pattern', recurse body) | (pattern', body) <- branches]
        input result
      M.EStrcat left right -> M.EStrcat (recurse left) (recurse right)
      M.EError value typ -> M.EError (recurse value) typ
      M.EReturnBlob content mime typ ->
        M.EReturnBlob (recurse <$> content) (recurse mime) typ
      M.ERedirect value typ -> M.ERedirect (recurse value) typ
      M.EWrite value -> M.EWrite (recurse value)
      M.ESeq first second -> M.ESeq (recurse first) (recurse second)
      M.ELet name typ value body -> M.ELet name typ (recurse value) (recurse body)
      M.EClosure identifier captures -> M.EClosure identifier (map recurse captures)
      M.EQuery fields tables state query body initial ->
        M.EQuery fields tables state (recurse query) (recurse body) (recurse initial)
      M.EDml value failure -> M.EDml (recurse value) failure
      M.ENextval value -> M.ENextval (recurse value)
      M.ESetval sequence' value -> M.ESetval (recurse sequence') (recurse value)
      M.EUnurlify value typ optional -> M.EUnurlify (recurse value) typ optional
      M.EJavaScript mode value -> M.EJavaScript mode (recurse value)
      M.ESignalReturn value -> M.ESignalReturn (recurse value)
      M.ESignalBind signal continuation ->
        M.ESignalBind (recurse signal) (recurse continuation)
      M.ESignalSource value -> M.ESignalSource (recurse value)
      M.EServerCall call typ effect failure ->
        M.EServerCall (recurse call) typ effect failure
      M.ERecv channel typ -> M.ERecv (recurse channel) typ
      M.ESleep value -> M.ESleep (recurse value)
      M.ESpawn value -> M.ESpawn (recurse value)
      leaf -> leaf}

instrumentQuery :: String -> M.Expr -> M.Expr
instrumentQuery databaseSystem original = case collectApplications original of
  (headExpression, [query, callback, initial])
    | Just (tablesStatic, expressionsStatic, stateStatic) <- queryHead headExpression
    , Just tables <- nestedRowTypes at tablesStatic
    , Just expressions <- flatRowTypes at expressionsStatic
    , Just stateType <- staticType at stateStatic
    , cacheableQuery expressions tables ->
        makeInstrumentedQuery databaseSystem original headExpression
          query callback initial expressions tables stateType
  _ -> original
  where
    at = locatedSpan original

queryHead :: M.Expr -> Maybe (M.StaticArg, M.StaticArg, M.StaticArg)
queryHead expression = case locatedValue expression of
  M.EFfi "Basis" "query" [tables, expressions, state] ->
    Just (tables, expressions, state)
  M.EFfiApp "Basis" "query" [tables, expressions, state] [] ->
    Just (tables, expressions, state)
  _ -> Nothing

collectApplications :: M.Expr -> (M.Expr, [M.Expr])
collectApplications = go []
  where
    go arguments expression = case locatedValue expression of
      M.EApp function argument -> go (argument : arguments) function
      _ -> (expression, arguments)

flatRowTypes :: Span -> M.StaticArg -> Maybe [(String, M.Type)]
flatRowTypes at (M.StaticRow fields) = traverse rowField fields
  where
    rowField (M.StaticName name, typ) = (name,) <$> staticType at typ
    rowField _ = Nothing
flatRowTypes _ _ = Nothing

nestedRowTypes :: Span -> M.StaticArg -> Maybe [(String, [(String, M.Type)])]
nestedRowTypes at (M.StaticRow tables) = traverse table tables
  where
    table (M.StaticName name, fields) = (name,) <$> flatRowTypes at fields
    table _ = Nothing
nestedRowTypes _ _ = Nothing

staticType :: Span -> M.StaticArg -> Maybe M.Type
staticType _ (M.StaticType typ) = Just typ
staticType at (M.StaticFfi "Basis" "option" [element]) =
  Located at . M.TOption <$> staticType at element
staticType at (M.StaticFfi "Basis" "list" [element]) =
  Located at . M.TList <$> staticType at element
staticType at (M.StaticFfi "Basis" "transaction" [result]) = do
  resultType <- staticType at result
  pure (Located at (M.TFun (unitType at) resultType))
staticType at (M.StaticFfi "Basis" "source" []) = Just (Located at M.TSource)
staticType at (M.StaticFfi "Basis" "signal" [element]) =
  Located at . M.TSignal <$> staticType at element
staticType at (M.StaticFfi moduleName name _) =
  Just (Located at (M.TFfi moduleName name))
staticType _ _ = Nothing

cacheableQuery
  :: [(String, M.Type)]
  -> [(String, [(String, M.Type)])]
  -> Bool
cacheableQuery expressions tables =
  (any (cacheableType . snd) expressions
    || any (any (cacheableType . snd) . snd) tables)
    && uniqueColumnNames
  where
    names = map fst expressions <> concatMap (map fst . snd) tables
    uniqueColumnNames = length names == length (nub names)

cacheableType :: M.Type -> Bool
cacheableType typ = case locatedValue typ of
  M.TFfi "Basis" "blob" -> True
  M.TOption element -> case locatedValue element of
    M.TFfi "Basis" "blob" -> True
    _ -> False
  _ -> False

makeInstrumentedQuery
  :: String
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> M.Expr
  -> [(String, M.Type)]
  -> [(String, [(String, M.Type)])]
  -> M.Type
  -> M.Expr
makeInstrumentedQuery databaseSystem source queryFunction query callback initial expressions tables stateType =
  at (M.ECase missed
    [(falsePattern, cachedQuery), (truePattern, fillingQuery)]
    boolType transactionState)
  where
    location = locatedSpan source
    at = Located location
    boolType = Located location (M.TFfi "Basis" "bool")
    transactionState = Located location (M.TFun (unitType location) stateType)
    missed = at (M.EFfiApp "Basis" "filecache_missed" [] [])
    falsePattern = Located location
      (M.PCon M.Enum (M.PConFfi "Basis" "bool" "False" Nothing) Nothing)
    truePattern = Located location
      (M.PCon M.Enum (M.PConFfi "Basis" "bool" "True" Nothing) Nothing)
    originalStatic = queryStaticArguments queryFunction
    cachedFunction = queryFunction {locatedValue = case locatedValue queryFunction of
      M.EFfi moduleName name _ -> M.EFfi moduleName name (map unblobStatic originalStatic)
      M.EFfiApp moduleName name _ values ->
        M.EFfiApp moduleName name (map unblobStatic originalStatic) values
      value -> value}
    wrappedSql = at (M.EStrcat (text prefix) (at (M.EStrcat query (text suffix))))
    (prefix, suffix) = wrapperSql databaseSystem expressions tables
    cachedQuery = apply3 cachedFunction wrappedSql
      (restoringCallback location callback expressions tables stateType) initial
    fillingQuery = apply3 queryFunction query
      (fillingCallback location callback expressions tables stateType) initial
    text value = at (M.EPrim (PrimString NormalString (ByteString.pack value)))

queryStaticArguments :: M.Expr -> [M.StaticArg]
queryStaticArguments expression = case locatedValue expression of
  M.EFfi _ _ arguments -> arguments
  M.EFfiApp _ _ arguments _ -> arguments
  _ -> []

apply3 :: M.Expr -> M.Expr -> M.Expr -> M.Expr -> M.Expr
apply3 function first second third =
  let at = locatedSpan function
   in Located at (M.EApp
        (Located at (M.EApp (Located at (M.EApp function first)) second))
        third)

wrapperSql
  :: String
  -> [(String, M.Type)]
  -> [(String, [(String, M.Type)])]
  -> (String, String)
wrapperSql databaseSystem expressions tables =
  ("SELECT " <> intercalate ", " (map render columns) <> " FROM (", ") AS Wrap")
  where
    columns =
      [(name, typ) | (name, typ) <- expressions]
        <> [("vr__" <> table <> "__" <> name, typ)
           | (table, fields) <- tables, (name, typ) <- fields]
    render (name, typ)
      | cacheableType typ = case map toLower databaseSystem of
          "mysql" -> "SHA2(" <> qualified name <> ", 512) AS " <> identifier name
          _ -> "encode(digest(" <> qualified name
            <> ", 'sha512'), 'hex') AS " <> identifier name
      | otherwise = qualified name <> " AS " <> identifier name
    qualified name = "Wrap." <> identifier name
    identifier = sqlIdentifier databaseSystem

sqlIdentifier :: String -> String -> String
sqlIdentifier databaseSystem value = delimiter : concatMap escape value <> [delimiter]
  where
    delimiter = if map toLower databaseSystem == "mysql" then '`' else '"'
    escape character
      | character == delimiter = [delimiter, delimiter]
      | otherwise = [character]

restoringCallback
  :: Span
  -> M.Expr
  -> [(String, M.Type)]
  -> [(String, [(String, M.Type)])]
  -> M.Type
  -> M.Expr
restoringCallback at callback expressions tables stateType =
  Located at (M.EAbs "uncached" uncachedRowType innerType
    (Located at (M.EAbs "state" stateType transactionState originalCall)))
  where
    uncachedRowType = rowType at (map unblobField expressions)
      [(name, map unblobField fields) | (name, fields) <- tables]
    originalRow = buildRow at restoreValue expressions tables
    originalCall = Located at (M.EApp
      (Located at (M.EApp (liftExpression 0 2 callback) originalRow))
      (Located at (M.ERel 0)))
    transactionState = Located at (M.TFun (unitType at) stateType)
    innerType = Located at (M.TFun stateType transactionState)

fillingCallback
  :: Span
  -> M.Expr
  -> [(String, M.Type)]
  -> [(String, [(String, M.Type)])]
  -> M.Type
  -> M.Expr
fillingCallback at callback expressions tables stateType =
  Located at (M.EAbs "row" originalRowType innerType
    (Located at (M.EAbs "state" stateType transactionState body)))
  where
    originalRowType = rowType at expressions tables
    originalCall = Located at (M.EApp
      (Located at (M.EApp (liftExpression 0 2 callback) (Located at (M.ERel 1))))
      (Located at (M.ERel 0)))
    body = foldr (cacheThen at) originalCall
      (cacheableAccesses at expressions tables)
    transactionState = Located at (M.TFun (unitType at) stateType)
    innerType = Located at (M.TFun stateType transactionState)

rowType
  :: Span
  -> [(String, M.Type)]
  -> [(String, [(String, M.Type)])]
  -> M.Type
rowType at expressions tables = Located at (M.TRecord
  (expressions <> [(name, Located at (M.TRecord fields)) | (name, fields) <- tables]))

unblobField :: (String, M.Type) -> (String, M.Type)
unblobField (name, typ) = (name, unblobType typ)

unblobType :: M.Type -> M.Type
unblobType typ = typ {locatedValue = case locatedValue typ of
  M.TFun domain range -> M.TFun (unblobType domain) (unblobType range)
  M.TRecord fields -> M.TRecord (map unblobField fields)
  M.TFfi "Basis" "blob" -> M.TFfi "Basis" "string"
  M.TOption element -> M.TOption (unblobType element)
  M.TList element -> M.TList (unblobType element)
  M.TSignal element -> M.TSignal (unblobType element)
  value -> value}

unblobStatic :: M.StaticArg -> M.StaticArg
unblobStatic argument = case argument of
  M.StaticType typ -> M.StaticType (unblobType typ)
  M.StaticRow fields -> M.StaticRow
    [(unblobStatic name, unblobStatic typ) | (name, typ) <- fields]
  M.StaticTuple values -> M.StaticTuple (map unblobStatic values)
  M.StaticFfi "Basis" "blob" values ->
    M.StaticFfi "Basis" "string" (map unblobStatic values)
  M.StaticFfi moduleName name values ->
    M.StaticFfi moduleName name (map unblobStatic values)
  M.StaticLambda body -> M.StaticLambda (unblobStatic body)
  M.StaticApply function value ->
    M.StaticApply (unblobStatic function) (unblobStatic value)
  M.StaticProject record index -> M.StaticProject (unblobStatic record) index
  M.StaticConcat left right -> M.StaticConcat (unblobStatic left) (unblobStatic right)
  value -> value

buildRow
  :: Span
  -> (Span -> M.Expr -> M.Type -> M.Expr)
  -> [(String, M.Type)]
  -> [(String, [(String, M.Type)])]
  -> M.Expr
buildRow at convert expressions tables = Located at (M.ERecord
  ([ (M.StaticName name, convert at (field at (Located at (M.ERel 1)) name) typ, typ)
   | (name, typ) <- expressions
   ]
   <> [ (M.StaticName table, tableRecord table fields, Located at (M.TRecord fields))
      | (table, fields) <- tables
      ]))
  where
    tableRecord table fields = Located at (M.ERecord
      [ ( M.StaticName name
        , convert at (field at (field at (Located at (M.ERel 1)) table) name) typ
        , typ
        )
      | (name, typ) <- fields
      ])

field :: Span -> M.Expr -> String -> M.Expr
field at record name = Located at (M.EField record (M.StaticName name))

restoreValue :: Span -> M.Expr -> M.Type -> M.Expr
restoreValue at value typ = case locatedValue typ of
  M.TFfi "Basis" "blob" -> check value
  M.TOption element | isBlob element -> Located at (M.ECase value
    [ (Located at (M.PNone stringType), Located at (M.ENone blobType))
    , ( Located at (M.PSome stringType (Located at (M.PVar "hash" stringType)))
      , Located at (M.ESome blobType (check (Located at (M.ERel 0)))))
    ]
    (Located at (M.TOption stringType)) (Located at (M.TOption blobType)))
  _ -> value
  where
    stringType = Located at (M.TFfi "Basis" "string")
    blobType = Located at (M.TFfi "Basis" "blob")
    isBlob candidate = case locatedValue candidate of
      M.TFfi "Basis" "blob" -> True
      _ -> False
    check hash = Located at
      (M.EFfiApp "Basis" "check_filecache" [] [(hash, stringType)])

cacheableAccesses
  :: Span
  -> [(String, M.Type)]
  -> [(String, [(String, M.Type)])]
  -> [(M.Expr, M.Type)]
cacheableAccesses at expressions tables = filter (cacheableType . snd)
  ([ (field at (Located at (M.ERel 1)) name, typ)
   | (name, typ) <- expressions
   ]
   <> [ (field at (field at (Located at (M.ERel 1)) table) name, typ)
      | (table, fields) <- tables, (name, typ) <- fields
      ])

cacheThen :: Span -> (M.Expr, M.Type) -> M.Expr -> M.Expr
cacheThen at (value, typ) rest = Located at (M.ESeq action rest)
  where
    unit = unitType at
    blob = Located at (M.TFfi "Basis" "blob")
    action = case locatedValue typ of
      M.TFfi "Basis" "blob" -> cache value
      M.TOption element -> Located at (M.ECase value
        [ (Located at (M.PNone element), Located at (M.ERecord []))
        , ( Located at (M.PSome element (Located at (M.PVar "blob" element)))
          , cache (Located at (M.ERel 0))
          )
        ] typ unit)
      _ -> Located at (M.ERecord [])
    cache contents = Located at
      (M.EFfiApp "Basis" "cache_file" [] [(contents, blob)])

unitType :: Span -> M.Type
unitType at = Located at (M.TRecord [])

patternBindingCount :: M.Pattern -> Int
patternBindingCount pattern' = case locatedValue pattern' of
  M.PVar {} -> 1
  M.PPrim {} -> 0
  M.PCon _ _ nested -> maybe 0 patternBindingCount nested
  M.PRecord fields -> sum [patternBindingCount nested | (_, nested, _) <- fields]
  M.PNone {} -> 0
  M.PSome _ nested -> patternBindingCount nested

liftExpression :: Int -> Int -> M.Expr -> M.Expr
liftExpression cutoff amount = walk 0
  where
    walk bound expression = expression {locatedValue = case locatedValue expression of
      M.ERel index
        | index >= cutoff + bound -> M.ERel (index + amount)
        | otherwise -> M.ERel index
      M.ECon kind constructor payload -> M.ECon kind constructor (walk bound <$> payload)
      M.ESome typ value -> M.ESome typ (walk bound value)
      M.EFfiApp moduleName name staticArguments arguments ->
        M.EFfiApp moduleName name staticArguments
          [(walk bound value, typ) | (value, typ) <- arguments]
      M.EApp function argument -> M.EApp (walk bound function) (walk bound argument)
      M.EAbs name domain range body -> M.EAbs name domain range (walk (bound + 1) body)
      M.EStaticApp function argument -> M.EStaticApp (walk bound function) argument
      M.EUnop operator value -> M.EUnop operator (walk bound value)
      M.EBinop intness operator left right ->
        M.EBinop intness operator (walk bound left) (walk bound right)
      M.ERecord fields -> M.ERecord
        [(name, walk bound value, typ) | (name, value, typ) <- fields]
      M.EField record field' -> M.EField (walk bound record) field'
      M.ERecordConcat left right -> M.ERecordConcat (walk bound left) (walk bound right)
      M.ERecordCut record fields -> M.ERecordCut (walk bound record) fields
      M.ECase scrutinee branches input result -> M.ECase
        (walk bound scrutinee)
        [(pattern', walk (bound + patternBindingCount pattern') body)
        | (pattern', body) <- branches]
        input result
      M.EStrcat left right -> M.EStrcat (walk bound left) (walk bound right)
      M.EError value typ -> M.EError (walk bound value) typ
      M.EReturnBlob content mime typ ->
        M.EReturnBlob (walk bound <$> content) (walk bound mime) typ
      M.ERedirect value typ -> M.ERedirect (walk bound value) typ
      M.EWrite value -> M.EWrite (walk bound value)
      M.ESeq first second -> M.ESeq (walk bound first) (walk bound second)
      M.ELet name typ value body ->
        M.ELet name typ (walk bound value) (walk (bound + 1) body)
      M.EClosure identifier captures -> M.EClosure identifier (map (walk bound) captures)
      M.EQuery fields tables state query body initial -> M.EQuery fields tables state
        (walk bound query) (walk (bound + 2) body) (walk bound initial)
      M.EDml value failure -> M.EDml (walk bound value) failure
      M.ENextval value -> M.ENextval (walk bound value)
      M.ESetval sequence' value -> M.ESetval (walk bound sequence') (walk bound value)
      M.EUnurlify value typ optional -> M.EUnurlify (walk bound value) typ optional
      M.EJavaScript mode value -> M.EJavaScript mode (walk bound value)
      M.ESignalReturn value -> M.ESignalReturn (walk bound value)
      M.ESignalBind signal continuation ->
        M.ESignalBind (walk bound signal) (walk bound continuation)
      M.ESignalSource value -> M.ESignalSource (walk bound value)
      M.EServerCall call typ effect failure ->
        M.EServerCall (walk bound call) typ effect failure
      M.ERecv channel typ -> M.ERecv (walk bound channel) typ
      M.ESleep value -> M.ESleep (walk bound value)
      M.ESpawn value -> M.ESpawn (walk bound value)
      leaf -> leaf}
