module Vr.Parse.Expression.SQL
  ( SqlFrom (..)
  , parseSqlQuery
  , parseSqlQuery1
  , parseSqlExpr
  , parseSqlFrom
  , parseSqlInsert
  , parseSqlUpdate
  , parseSqlDelete
  , parseSqlFieldIdentifier
  , parseSqlDmlTable
  , recordExpr
  ) where

import Control.Monad (unless, when)
import {-# SOURCE #-} Vr.Parse.Expression (parseExpr)
import Vr.Parse.Core
import Vr.Parse.Lexer
import Vr.Parse.Type
import Vr.Source
data SqlSelection
  = SqlSelectStar
  | SqlSelectItems ![SqlSelectItem]

data SqlSelectItem
  = SqlSelectExpression !(Maybe SCon) !SExpr
  | SqlSelectField !SCon !SCon
  | SqlSelectFields !SCon !SCon
  | SqlSelectStarFields !SCon

data SqlFrom = SqlFrom
  { sqlFromNames :: ![SCon]
  , sqlFromExpression :: !SExpr
  }

sameSqlName :: SCon -> SCon -> Bool
sameSqlName left right = sqlName left == sqlName right
  where
    sqlName constructor = case locatedValue constructor of
      SCName name -> Just name
      SCVar [] name -> Just name
      _ -> Nothing

parseSqlQuery :: Parser SExpr
parseSqlQuery = do
  rows <- parseSqlQuery1
  orderBy <- parseSqlOrderBy
  limit <- parseSqlLimit
  offset <- parseSqlOffset
  let at = foldSpans (locatedSpan rows) [locatedSpan orderBy, locatedSpan limit, locatedSpan offset]
      arguments = recordExpr at [("Rows", rows), ("OrderBy", orderBy), ("Limit", limit), ("Offset", offset)]
  pure (Located at (SEApp (basisVar at "sql_query") arguments))

parseSqlQuery1 :: Parser SExpr
parseSqlQuery1 = do
  first <- parseSqlSelect
  parseRelations first
  where
    parseRelations left = do
      next <- peekText
      case next of
        Just relation | relation `elem` ["UNION", "INTERSECT", "EXCEPT"] -> do
          _ <- consumeToken
          allRows <- acceptText "ALL"
          right <- parseSqlSelect
          let at = mergeSpans (locatedSpan left) (locatedSpan right)
              operation = case relation of
                "UNION" -> "union"
                "INTERSECT" -> "intersect"
                _ -> "except"
              related = sqlRelation at operation allRows left right
          parseRelations related
        _ -> pure left

parseSqlSelect :: Parser SExpr
parseSqlSelect = do
  start <- expectText "SELECT"
  distinct <- acceptText "DISTINCT"
  selection <- parseSqlSelection
  _ <- expectText "FROM"
  from <- parseSqlFrom
  whereExpression <- ifM (acceptText "WHERE") parseSqlExpr (pure (sqlInject noSpan (basisVar noSpan "True")))
  groupBy <- parseSqlGroupBy from
  having <- ifM (acceptText "HAVING") parseSqlExpr (pure (sqlInject noSpan (basisVar noSpan "True")))
  let endAt = locatedSpan having
      at = mergeSpans (tokenSpan start) endAt
      (emptyTables, selectedFields, selectedExpressions) = elaborateSqlSelection at from selection
      distinctExpr = basisVar at (if distinct then "True" else "False")
      subsetAll = Located at (SECApp (basisVar at "sql_subset_all") (wildRowKind at (Located at (SKRecord (Located at SKType)))))
      groupExpression = maybe subsetAll id groupBy
      queryHead = Located at (SECApp (basisVar at "sql_query1") (Located at (SCRecord [(name, Located at SCUnit) | name <- emptyTables])))
      arguments =
        recordExpr
          at
          [ ("Distinct", distinctExpr)
          , ("From", sqlFromExpression from)
          , ("Where", whereExpression)
          , ("GroupBy", groupExpression)
          , ("Having", having)
          , ("SelectFields", Located at (SECApp (basisVar at "sql_subset") selectedFields))
          , ("SelectExps", selectedExpressions)
          ]
  pure (Located at (SEApp queryHead arguments))

parseSqlSelection :: Parser SqlSelection
parseSqlSelection = do
  star <- acceptText "*"
  if star
    then pure SqlSelectStar
    else do
      first <- parseSqlSelectItem
      rest <- parseSeparated "," parseSqlSelectItem
      pure (SqlSelectItems (first : rest))

parseSqlSelectItem :: Parser SqlSelectItem
parseSqlSelectItem = do
  dynamicFields <- sqlDynamicFieldsAhead
  if dynamicFields
    then do
      table <- parseSqlTableIdentifierOrLower
      _ <- expectText "."
      _ <- expectText "{"
      _ <- expectText "{"
      fields <- parseCon
      _ <- expectText "}"
      _ <- expectText "}"
      pure (SqlSelectFields table fields)
    else do
      starFields <- sqlStarFieldsAhead
      if starFields
        then do
          table <- parseSqlTableIdentifierOrLower
          _ <- expectText "."
          _ <- expectText "*"
          pure (SqlSelectStarFields table)
        else do
          plainField <- sqlPlainFieldAhead
          if plainField
            then do
              table <- parseSqlTableIdentifierOrLower
              _ <- expectText "."
              field <- parseSqlFieldIdentifier
              pure (SqlSelectField table field)
            else do
              expression <- parseSqlExpr
              alias <- ifM (acceptText "AS") (Just <$> parseSqlFieldIdentifier) (pure Nothing)
              pure (SqlSelectExpression alias expression)

sqlDynamicFieldsAhead :: Parser Bool
sqlDynamicFieldsAhead = do
  first <- peekKind
  dot <- peekTextN 1
  open1 <- peekTextN 2
  open2 <- peekTextN 3
  pure (case first of
    Just (TokenIdentifier _) -> dot == Just "." && open1 == Just "{" && open2 == Just "{"
    Just (TokenConstructor _) -> dot == Just "." && open1 == Just "{" && open2 == Just "{"
    _ -> False)

sqlStarFieldsAhead :: Parser Bool
sqlStarFieldsAhead = do
  first <- peekKind
  dot <- peekTextN 1
  star <- peekTextN 2
  pure (isSqlTableToken first && dot == Just "." && star == Just "*")

sqlPlainFieldAhead :: Parser Bool
sqlPlainFieldAhead = do
  first <- peekKind
  dot <- peekTextN 1
  field <- peekKindN 2
  following <- peekTextN 3
  pure
    ( isSqlTableToken first
        && dot == Just "."
        && case field of
          Just (TokenConstructor _) -> following == Just "," || following == Just "FROM"
          _ -> False
    )

isSqlTableToken :: Maybe TokenKind -> Bool
isSqlTableToken token = case token of
  Just (TokenIdentifier _) -> True
  Just (TokenConstructor _) -> True
  _ -> False

elaborateSqlSelection :: Span -> SqlFrom -> SqlSelection -> ([SCon], SCon, SExpr)
elaborateSqlSelection at from selection = case selection of
  SqlSelectStar ->
    let pair name =
          ( name
          , Located at (SCTuple [wildRowKind at (Located at SKType), Located at (SCRecord [])])
          )
     in ([], Located at (SCRecord (map pair (sqlFromNames from))), Located at (SERecord [] False))
  SqlSelectItems items ->
    let expressions = [(alias, expression) | SqlSelectExpression alias expression <- items]
        numbered = zip [(1 :: Int) ..] expressions
        named =
          [ ( maybe (Located at (SCName (show index))) id maybeName
            , Located at (SEApp (basisVar at "sql_window") expression)
            )
          | (index, (maybeName, expression)) <- numbered
          ]
        selectedFor table =
          foldr
            (\item (everything, rest) -> case item of
                SqlSelectField selected field | sameSqlName table selected ->
                  (everything, Located at (SCConcat (Located at (SCRecord [(field, Located at (SCWild (Located at SKType)))])) rest))
                SqlSelectFields selected fields | sameSqlName table selected ->
                  (everything, Located at (SCConcat fields rest))
                SqlSelectStarFields selected | sameSqlName table selected -> (True, rest)
                _ -> (everything, rest))
            (False, Located at (SCRecord []))
            items
        selections = [(name, selectedFor name) | name <- sqlFromNames from]
        empties = [name | (name, (everything, selected)) <- selections, not everything && isEmptySqlRow selected]
        tableSelection (everything, selected)
          | everything = Located at (SCTuple [wildRowKind at (Located at SKType), Located at (SCRecord [])])
          | otherwise = Located at (SCTuple [selected, wildRowKind at (Located at SKType)])
        tableFields = Located at (SCRecord [(name, tableSelection selected) | (name, selected) <- selections])
     in (empties, tableFields, Located at (SERecord named False))
  where
    isEmptySqlRow constructor = case locatedValue constructor of
      SCRecord [] -> True
      _ -> False

parseSqlFrom :: Parser SqlFrom
parseSqlFrom = do
  first <- parseSqlFromItem
  parseCommaItems first
  where
    parseCommaItems accumulated = do
      comma <- acceptText ","
      if not comma
        then pure accumulated
        else do
          right <- parseSqlFromItem
          let at = mergeSpans (locatedSpan (sqlFromExpression accumulated)) (locatedSpan (sqlFromExpression right))
              headExpression = Located at (SEApp (basisVar at "sql_from_comma") (sqlFromExpression accumulated))
              combined = Located at (SEApp headExpression (sqlFromExpression right))
          parseCommaItems (SqlFrom (sqlFromNames accumulated <> sqlFromNames right) combined)

parseSqlFromItem :: Parser SqlFrom
parseSqlFromItem = do
  left <- parseSqlFromAtom
  parseJoins left
  where
    parseJoins accumulated = do
      next <- peekText
      case next of
        Just joinStart | joinStart `elem` ["JOIN", "INNER", "CROSS", "LEFT", "RIGHT", "FULL"] -> do
          (functionName, needsCondition) <- parseJoinKind
          right <- parseSqlFromAtom
          condition <- if needsCondition
            then expectText "ON" *> parseSqlExpr
            else pure (sqlInject noSpan (basisVar noSpan "True"))
          let at = mergeSpans (locatedSpan (sqlFromExpression accumulated)) (locatedSpan condition)
              headExpression = Located at (SEApp (Located at (SEApp (basisVar at functionName) (sqlFromExpression accumulated))) (sqlFromExpression right))
              joined = Located at (SEApp headExpression condition)
          parseJoins (SqlFrom (sqlFromNames accumulated <> sqlFromNames right) joined)
        _ -> pure accumulated

parseJoinKind :: Parser (String, Bool)
parseJoinKind = do
  next <- peekText
  case next of
    Just "JOIN" -> expectText "JOIN" *> pure ("sql_inner_join", True)
    Just "INNER" -> expectText "INNER" *> expectText "JOIN" *> pure ("sql_inner_join", True)
    Just "CROSS" -> expectText "CROSS" *> expectText "JOIN" *> pure ("sql_inner_join", False)
    Just "LEFT" -> expectText "LEFT" *> optionalText "OUTER" *> expectText "JOIN" *> pure ("sql_left_join", True)
    Just "RIGHT" -> expectText "RIGHT" *> optionalText "OUTER" *> expectText "JOIN" *> pure ("sql_right_join", True)
    Just "FULL" -> expectText "FULL" *> optionalText "OUTER" *> expectText "JOIN" *> pure ("sql_full_join", True)
    _ -> parseFailure "sql-join" "Expected a SQL join"

parseSqlFromAtom :: Parser SqlFrom
parseSqlFromAtom = do
  next <- peekKind
  case next of
    Just (TokenIdentifier tableName) -> do
      token <- consumeToken
      alias <- ifM (acceptText "AS") parseSqlTableIdentifier (pure (Located (tokenSpan token) (SCName (capitalize tableName))))
      let at = mergeSpans (tokenSpan token) (locatedSpan alias)
          tableValue = Located at (SEVar [] tableName Infer)
          fromHead = Located at (SECApp (basisVar at "sql_from_table") alias)
      pure (SqlFrom [alias] (Located at (SEApp fromHead tableValue)))
    Just (TokenPunctuation "{") -> do
      start <- expectText "{"
      _ <- expectText "{"
      expression <- parseExpr
      _ <- expectText "}"
      _ <- expectText "}"
      _ <- expectText "AS"
      alias <- parseSqlTableIdentifier
      let at = mergeSpans (tokenSpan start) (locatedSpan alias)
          fromHead = Located at (SECApp (basisVar at "sql_from_table") alias)
      pure (SqlFrom [alias] (Located at (SEApp fromHead expression)))
    Just (TokenPunctuation "(") -> do
      start <- expectText "("
      queryAhead <- atText "SELECT"
      splicedAhead <- (&&) <$> atText "{" <*> ((== Just "{") <$> peekTextN 1)
      if queryAhead
        then do
          query <- parseSqlQuery
          _ <- expectText ")"
          _ <- expectText "AS"
          alias <- parseSqlTableIdentifier
          let at = mergeSpans (tokenSpan start) (locatedSpan alias)
              fromHead = Located at (SECApp (basisVar at "sql_from_query") alias)
          pure (SqlFrom [alias] (Located at (SEApp fromHead query)))
        else if splicedAhead
          then do
            _ <- expectText "{"
            _ <- expectText "{"
            query <- parseExpr
            _ <- expectText "}"
            _ <- expectText "}"
            _ <- expectText ")"
            _ <- expectText "AS"
            alias <- parseSqlTableIdentifier
            let at = mergeSpans (tokenSpan start) (locatedSpan alias)
                fromHead = Located at (SECApp (basisVar at "sql_from_query") alias)
            pure (SqlFrom [alias] (Located at (SEApp fromHead query)))
          else do
            grouped <- parseSqlFromItem
            _ <- expectText ")"
            pure grouped
    _ -> parseFailure "sql-from" "Expected a SQL table or subquery"

parseSqlTableIdentifier :: Parser SCon
parseSqlTableIdentifier = do
  next <- peekKind
  case next of
    Just (TokenConstructor name) -> consumeLocatedCon (SCName name)
    Just (TokenPunctuation "{") -> expectText "{" *> parseCon <* expectText "}"
    _ -> parseFailure "sql-table-name" "Expected a SQL table name"

parseSqlFieldIdentifier :: Parser SCon
parseSqlFieldIdentifier = parseSqlTableIdentifier

parseSqlGroupBy :: SqlFrom -> Parser (Maybe SExpr)
parseSqlGroupBy from = do
  grouped <- acceptText "GROUP"
  if not grouped
    then pure Nothing
    else do
      _ <- expectText "BY"
      first <- parseSqlGroupItem
      rest <- parseSeparated "," parseSqlGroupItem
      let items = first : rest
          at = foldSpans (locatedSpan (fst first)) [locatedSpan field | (_, field) <- rest]
          rows =
            [ ( alias
              , Located at (SCTuple [Located at (SCRecord [(field, wildType at) | (table, field) <- items, sameSqlName table alias]), wildRowKind at (Located at SKType)])
              )
            | alias <- sqlFromNames from
            ]
      pure (Just (Located at (SECApp (basisVar at "sql_subset") (Located at (SCRecord rows)))))

parseSqlGroupItem :: Parser (SCon, SCon)
parseSqlGroupItem = do
  table <- parseSqlTableIdentifierOrLower
  _ <- expectText "."
  field <- parseSqlFieldIdentifier
  pure (table, field)

parseSqlTableIdentifierOrLower :: Parser SCon
parseSqlTableIdentifierOrLower = do
  next <- peekKind
  case next of
    Just (TokenIdentifier name) -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SCName (capitalize name)))
    _ -> parseSqlTableIdentifier

parseSqlOrderBy :: Parser SExpr
parseSqlOrderBy = do
  ordered <- acceptText "ORDER"
  if not ordered
    then pure (sqlOrderNil noSpan)
    else do
      _ <- expectText "BY"
      randomOrder <- acceptText "RANDOM"
      if randomOrder
        then do
          unit <- (== Just TokenUnit) <$> peekKind
          when unit (consumeToken >> pure ())
          pure (basisVar noSpan "sql_order_by_random")
        else do
          supplied <- atText "{"
          secondBrace <- (== Just "{") <$> peekTextN 1
          if supplied && secondBrace
            then do
              _ <- expectText "{"
              _ <- expectText "{"
              _ <- expectText "{"
              expression <- parseExpr
              _ <- expectText "}"
              _ <- expectText "}"
              _ <- expectText "}"
              pure expression
            else do
              first <- parseSqlOrderItem
              rest <- parseSeparated "," parseSqlOrderItem
              let items = first : rest
                  at = foldSpans (locatedSpan (fst first)) [locatedSpan expression | (expression, _) <- rest]
              pure (foldr (\(expression, direction) tailExpression -> Located at (SEApp (Located at (SEApp (Located at (SEApp (basisVar at "sql_order_by_Cons") expression)) direction)) tailExpression)) (sqlOrderNil at) items)

parseSqlOrderItem :: Parser (SExpr, SExpr)
parseSqlOrderItem = do
  expression <- parseSqlExpr
  direction <- do
    next <- peekText
    case next of
      Just "ASC" -> expectText "ASC" *> pure (basisVar (locatedSpan expression) "sql_asc")
      Just "DESC" -> expectText "DESC" *> pure (basisVar (locatedSpan expression) "sql_desc")
      Just "{" -> do
        _ <- expectText "{"
        supplied <- parseExpr
        _ <- expectText "}"
        pure supplied
      _ -> pure (basisVar (locatedSpan expression) "sql_asc")
  pure (expression, direction)

sqlOrderNil :: Span -> SExpr
sqlOrderNil at = Located at (SECApp (basisVar at "sql_order_by_Nil") (wildRowKind at (Located at SKType)))

parseSqlLimit :: Parser SExpr
parseSqlLimit = do
  limited <- acceptText "LIMIT"
  if not limited
    then pure (basisVar noSpan "sql_no_limit")
    else do
      allRows <- acceptText "ALL"
      if allRows
        then pure (basisVar noSpan "sql_no_limit")
        else do
          amount <- parseSqlInteger
          pure (Located (locatedSpan amount) (SEApp (basisVar (locatedSpan amount) "sql_limit") amount))

parseSqlOffset :: Parser SExpr
parseSqlOffset = do
  offset <- acceptText "OFFSET"
  if not offset
    then pure (basisVar noSpan "sql_no_offset")
    else do
      amount <- parseSqlInteger
      pure (Located (locatedSpan amount) (SEApp (basisVar (locatedSpan amount) "sql_offset") amount))

parseSqlInteger :: Parser SExpr
parseSqlInteger = do
  next <- peekKind
  case next of
    Just (TokenInt value) -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SEPrim (PrimInt value)))
    Just (TokenPunctuation "{") -> expectText "{" *> parseExpr <* expectText "}"
    _ -> parseFailure "sql-integer" "Expected a SQL integer expression"

parseSqlExpr :: Parser SExpr
parseSqlExpr = parseSqlExprPrec 0

parseSqlExprPrec :: Int -> Parser SExpr
parseSqlExprPrec precedenceFloor = do
  left <- parseSqlPrefix
  parseSqlInfix precedenceFloor left

parseSqlPrefix :: Parser SExpr
parseSqlPrefix = do
  next <- peekText
  case next of
    Just "NOT" -> do
      start <- expectText "NOT"
      argument <- parseSqlExprPrec 60
      pure (sqlUnary (mergeSpans (tokenSpan start) (locatedSpan argument)) "not" argument)
    Just "-" -> do
      start <- expectText "-"
      argument <- parseSqlExprPrec 60
      pure (sqlUnary (mergeSpans (tokenSpan start) (locatedSpan argument)) "neg" argument)
    Just "IF" -> do
      start <- expectText "IF"
      condition <- parseSqlExpr
      _ <- expectText "THEN"
      whenTrue <- parseSqlExpr
      _ <- expectText "ELSE"
      whenFalse <- parseSqlExpr
      let at = mergeSpans (tokenSpan start) (locatedSpan whenFalse)
      pure (applyMany at (basisVar at "sql_if_then_else") [condition, whenTrue, whenFalse])
    _ -> parseSqlAtom

parseSqlAtom :: Parser SExpr
parseSqlAtom = do
  next <- peekKind
  case next of
    Just (TokenKeyword "TRUE") -> injectOrdinary (basisVar noSpan "True")
    Just (TokenKeyword "FALSE") -> injectOrdinary (basisVar noSpan "False")
    Just (TokenInt value) -> injectPrimitive (PrimInt value)
    Just (TokenFloat value) -> injectPrimitive (PrimFloat value)
    Just (TokenString value) -> injectPrimitive (PrimString NormalString value)
    Just (TokenKeyword "CURRENT_TIMESTAMP") -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SEApp (basisVar (tokenSpan token) "sql_nfunc") (basisVar (tokenSpan token) "sql_current_timestamp")))
    Just (TokenKeyword "NULL") -> do
      token <- consumeToken
      pure (sqlInject (tokenSpan token) (basisVar (tokenSpan token) "None"))
    Just (TokenKeyword "COUNT") -> parseSqlCount
    Just (TokenKeyword aggregate) | aggregate `elem` ["AVG", "SUM", "MIN", "MAX"] -> parseSqlAggregate aggregate
    Just (TokenKeyword "RANK") -> parseSqlRank
    Just (TokenKeyword "COALESCE") -> parseSqlCoalesce
    Just (TokenConstructor _) -> parseSqlNamedAtom
    Just (TokenIdentifier _) -> do
      following <- peekKindN 1
      case following of
        Just (TokenPunctuation ".") -> parseSqlLowerField
        _ -> parseSqlFunction
    Just (TokenPunctuation "{") -> parseSqlSplice
    Just (TokenPunctuation "(") -> do
      _ <- expectText "("
      isQuery <- atText "SELECT"
      expression <- if isQuery
        then do
          query <- parseSqlQuery
          pure (Located (locatedSpan query) (SEApp (basisVar (locatedSpan query) "sql_subquery") query))
        else parseSqlExpr
      _ <- expectText ")"
      pure expression
    _ -> parseFailure "sql-expression" "Expected a SQL expression"
  where
    injectOrdinary expression = consumeToken *> pure (sqlInject (locatedSpan expression) expression)
    injectPrimitive primitive = do
      token <- consumeToken
      pure (sqlInject (tokenSpan token) (Located (tokenSpan token) (SEPrim primitive)))

parseSqlNamedAtom :: Parser SExpr
parseSqlNamedAtom = do
  (name, token) <- expectConstructor
  field <- acceptText "."
  if field
    then do
      fieldName <- parseSqlFieldIdentifier
      let at = mergeSpans (tokenSpan token) (locatedSpan fieldName)
          fieldHead = Located at (SECApp (Located at (SECApp (basisVar at "sql_field") (Located at (SCName name)))) fieldName)
      pure fieldHead
    else
      let at = tokenSpan token
       in pure (Located at (SECApp (basisVar at "sql_exp") (Located at (SCName name))))

parseSqlLowerField :: Parser SExpr
parseSqlLowerField = do
  (name, token) <- expectIdentifier
  _ <- expectText "."
  fieldName <- parseSqlFieldIdentifier
  let at = mergeSpans (tokenSpan token) (locatedSpan fieldName)
      tableName = Located (tokenSpan token) (SCName (capitalize name))
  pure (Located at (SECApp (Located at (SECApp (basisVar at "sql_field") tableName)) fieldName))

parseSqlFunction :: Parser SExpr
parseSqlFunction = do
  (name, token) <- expectIdentifier
  _ <- expectText "("
  first <- parseSqlExpr
  second <- ifM (acceptText ",") (Just <$> parseSqlExpr) (pure Nothing)
  end <- expectText ")"
  let at = mergeSpans (tokenSpan token) (tokenSpan end)
      functionValue = basisVar at ("sql_" <> name)
      headName = if maybe False (const True) second then "sql_bfunc" else "sql_ufunc"
  pure (applyMany at (basisVar at headName) (functionValue : first : maybe [] (: []) second))

parseSqlSplice :: Parser SExpr
parseSqlSplice = do
  start <- expectText "{"
  injected <- acceptText "["
  expression <- parseExpr
  when injected (expectText "]" >> pure ())
  end <- expectText "}"
  let at = mergeSpans (tokenSpan start) (tokenSpan end)
  pure (if injected then sqlInject at expression else expression)

parseSqlCount :: Parser SExpr
parseSqlCount = do
  start <- expectText "COUNT"
  _ <- expectText "("
  star <- acceptText "*"
  expression <- if star then pure Nothing else Just <$> parseSqlExpr
  end <- expectText ")"
  window <- parseSqlWindow
  let at = mergeSpans (tokenSpan start) (maybe (tokenSpan end) (\(_, _, span') -> span') window)
  pure $ case (expression, window) of
    (Nothing, Nothing) -> basisVar at "sql_count"
    (Just argument, Nothing) -> applyMany at (basisVar at "sql_aggregate") [basisVar at "sql_count_col", argument]
    (Nothing, Just window') -> applySqlWindow at (basisVar at "sql_window_count") window'
    (Just argument, Just window') ->
      applySqlWindow at (applyMany at (basisVar at "sql_window_aggregate") [basisVar at "sql_count_col", argument]) window'

parseSqlAggregate :: String -> Parser SExpr
parseSqlAggregate aggregate = do
  start <- expectText aggregate
  _ <- expectText "("
  argument <- parseSqlExpr
  end <- expectText ")"
  window <- parseSqlWindow
  let at = mergeSpans (tokenSpan start) (maybe (tokenSpan end) (\(_, _, span') -> span') window)
      operation = basisVar at ("sql_" <> map asciiLower aggregate)
  pure $ case window of
    Nothing -> applyMany at (basisVar at "sql_aggregate") [operation, argument]
    Just window' -> applySqlWindow at (applyMany at (basisVar at "sql_window_aggregate") [operation, argument]) window'

parseSqlRank :: Parser SExpr
parseSqlRank = do
  start <- expectText "RANK"
  unit <- consumeToken
  unless (tokenKind unit == TokenUnit) (parseFailureAt (tokenSpan unit) "sql-rank" "Expected '()' after RANK")
  window <- parseSqlWindow
  let at = mergeSpans (tokenSpan start) (maybe (tokenSpan unit) (\(_, _, span') -> span') window)
      specification = maybe (basisVar at "sql_no_partition", sqlOrderNil at, at) id window
  pure (applySqlWindow at (basisVar at "sql_rank") specification)

-- The reference grammar treats OVER as part of COUNT, aggregate, and RANK
-- atoms.  A window consists of at most one partition expression followed by
-- the ordinary ORDER BY grammar (including RANDOM and supplied orderings).
parseSqlWindow :: Parser (Maybe (SExpr, SExpr, Span))
parseSqlWindow = do
  over <- acceptText "OVER"
  if not over
    then pure Nothing
    else do
      start <- expectText "("
      partitioned <- acceptText "PARTITION"
      partition <- if partitioned
        then do
          _ <- expectText "BY"
          expression <- parseSqlExpr
          pure (Located (locatedSpan expression) (SEApp (basisVar (locatedSpan expression) "sql_partition") expression))
        else pure (basisVar (tokenSpan start) "sql_no_partition")
      ordering <- parseSqlOrderBy
      end <- expectText ")"
      pure (Just (partition, ordering, mergeSpans (tokenSpan start) (tokenSpan end)))

applySqlWindow :: Span -> SExpr -> (SExpr, SExpr, Span) -> SExpr
applySqlWindow at function (partition, ordering, _) =
  applyMany at (basisVar at "sql_window_function") [function, partition, ordering]

parseSqlCoalesce :: Parser SExpr
parseSqlCoalesce = do
  start <- expectText "COALESCE"
  _ <- expectText "("
  first <- parseSqlExpr
  _ <- expectText ","
  second <- parseSqlExpr
  end <- expectText ")"
  let at = mergeSpans (tokenSpan start) (tokenSpan end)
  pure (applyMany at (basisVar at "sql_coalesce") [first, second])

data SqlOperator = SqlBinaryOperator !String | SqlIsNull

parseSqlInfix :: Int -> SExpr -> Parser SExpr
parseSqlInfix precedenceFloor left = do
  next <- peekText
  case next >>= sqlOperator of
    Just (operator, precedence) | precedence >= precedenceFloor -> do
      _ <- consumeToken
      case operator of
        SqlIsNull -> do
          _ <- expectText "NULL"
          let at = locatedSpan left
          parseSqlInfix precedenceFloor (Located at (SEApp (basisVar at "sql_is_null") left))
        SqlBinaryOperator name -> do
          right <- parseSqlExprPrec (precedence + 1)
          let at = mergeSpans (locatedSpan left) (locatedSpan right)
          parseSqlInfix precedenceFloor (sqlBinary at name left right)
    _ -> pure left

sqlOperator :: String -> Maybe (SqlOperator, Int)
sqlOperator spelling = case spelling of
  "OR" -> binary "or" 10
  "AND" -> binary "and" 20
  "=" -> binary "eq" 30
  "<>" -> binary "ne" 30
  "<" -> binary "lt" 30
  "<=" -> binary "le" 30
  ">" -> binary "gt" 30
  ">=" -> binary "ge" 30
  "LIKE" -> binary "like" 30
  "<->" -> binary "distance" 30
  "IS" -> Just (SqlIsNull, 30)
  "+" -> binary "plus" 40
  "-" -> binary "minus" 40
  "*" -> binary "times" 50
  "/" -> binary "div" 50
  "%" -> binary "mod" 50
  _ -> Nothing
  where
    binary name precedence = Just (SqlBinaryOperator name, precedence)

parseSqlInsert :: Parser SExpr
parseSqlInsert = do
  start <- expectText "INSERT"
  _ <- expectText "INTO"
  table <- parseSqlDmlTable
  _ <- expectText "("
  firstField <- parseSqlFieldIdentifier
  restFields <- parseSeparated "," parseSqlFieldIdentifier
  _ <- expectText ")"
  _ <- expectText "VALUES"
  _ <- expectText "("
  firstValue <- parseSqlExpr
  restValues <- parseSeparated "," parseSqlExpr
  end <- expectText ")"
  let fields = firstField : restFields
      values = firstValue : restValues
      at = mergeSpans (tokenSpan start) (tokenSpan end)
  unless (length fields == length values) (parseFailureAt at "insert-arity" "Length mismatch in INSERT field specification")
  pure (applyMany at (basisVar at "insert") [table, Located at (SERecord (zip fields values) False)])

parseSqlUpdate :: Parser SExpr
parseSqlUpdate = do
  start <- expectText "UPDATE"
  table <- parseSqlDmlTable
  _ <- expectText "SET"
  first <- parseSqlAssignment
  rest <- parseSeparated "," parseSqlAssignment
  _ <- expectText "WHERE"
  condition <- parseSqlExpr
  let at = mergeSpans (tokenSpan start) (locatedSpan condition)
      fields = Located at (SERecord [(name, dmlSqlFields value) | (name, value) <- first : rest] False)
      wildcard = Located at (SKRecord (Located at SKType))
      updateHead = Located at (SECApp (basisVar at "update") (Located at (SCWild wildcard)))
  pure (applyMany at updateHead [fields, table, dmlSqlFields condition])

parseSqlDelete :: Parser SExpr
parseSqlDelete = do
  start <- expectText "DELETE"
  _ <- expectText "FROM"
  table <- parseSqlDmlTable
  _ <- expectText "WHERE"
  condition <- parseSqlExpr
  let at = mergeSpans (tokenSpan start) (locatedSpan condition)
  pure (applyMany at (basisVar at "delete") [table, dmlSqlFields condition])

parseSqlAssignment :: Parser (SCon, SExpr)
parseSqlAssignment = do
  field <- parseSqlFieldIdentifier
  _ <- expectText "="
  value <- parseSqlExpr
  pure (field, value)

parseSqlDmlTable :: Parser SExpr
parseSqlDmlTable = do
  next <- peekKind
  case next of
    Just (TokenIdentifier name) -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SEVar [] name Infer))
    Just (TokenPunctuation "{") -> do
      _ <- expectText "{"
      _ <- expectText "{"
      expression <- parseExpr
      _ <- expectText "}"
      _ <- expectText "}"
      pure expression
    _ -> parseFailure "sql-table-expression" "Expected a table expression"

sqlInject :: Span -> SExpr -> SExpr
sqlInject at value = Located at (SEApp (basisVar at "sql_inject") value)

-- The reference grammar parses bare SQL constructor identifiers differently
-- while inside UPDATE and DELETE: @Id@ means @T.Id@, whereas outside DML it
-- denotes a named SQL expression.  Keep SQL parsing compositional and apply
-- that context-sensitive rewrite to the completed DML expression tree.
dmlSqlFields :: SExpr -> SExpr
dmlSqlFields expression = case locatedValue expression of
  SECApp function field
    | SEVar ["Basis"] "sql_exp" _ <- locatedValue function
    , SCName name <- locatedValue field ->
        let at = locatedSpan expression
            table = Located at (SCName "T")
            fieldName = Located (locatedSpan field) (SCName name)
            head' = Located at (SECApp (Located at (SECApp (basisVar at "sql_field") table)) fieldName)
         in head'
  SEAnnot value typ -> rebuild (SEAnnot (go value) typ)
  SEApp function argument -> rebuild (SEApp (go function) (go argument))
  SEAbs name annotation body -> rebuild (SEAbs name annotation (go body))
  SECApp function constructor -> rebuild (SECApp (go function) constructor)
  SECAbs explicitness name kind body -> rebuild (SECAbs explicitness name kind (go body))
  SEDisjoint left right body -> rebuild (SEDisjoint left right (go body))
  SEDisjointApp value -> rebuild (SEDisjointApp (go value))
  SEKAbs name body -> rebuild (SEKAbs name (go body))
  SERecord fields flexible -> rebuild (SERecord [(name, go value) | (name, value) <- fields] flexible)
  SEField record name -> rebuild (SEField (go record) name)
  SEConcat left right -> rebuild (SEConcat (go left) (go right))
  SECut record name -> rebuild (SECut (go record) name)
  SECutMulti record fields -> rebuild (SECutMulti (go record) fields)
  SECase scrutinee branches -> rebuild (SECase (go scrutinee) [(pattern', go body) | (pattern', body) <- branches])
  SELet declarations body -> rebuild (SELet (map mapDeclaration declarations) (go body))
  _ -> expression
  where
    go = dmlSqlFields
    rebuild value = expression {locatedValue = value}
    mapDeclaration declaration = declaration {locatedValue = case locatedValue declaration of
      SEDVal pattern' value -> SEDVal pattern' (go value)
      SEDValRec bindings -> SEDValRec [(name, annotation, go value) | (name, annotation, value) <- bindings]}

sqlUnary :: Span -> String -> SExpr -> SExpr
sqlUnary at name value = applyMany at (basisVar at "sql_unary") [basisVar at ("sql_" <> name), value]

sqlBinary :: Span -> String -> SExpr -> SExpr -> SExpr
sqlBinary at name left right = applyMany at (basisVar at "sql_binary") [basisVar at ("sql_" <> name), left, right]

sqlRelation :: Span -> String -> Bool -> SExpr -> SExpr -> SExpr
sqlRelation at name allRows left right =
  applyMany at (basisVar at "sql_relop") [basisVar at ("sql_" <> name), basisVar at (if allRows then "True" else "False"), left, right]

recordExpr :: Span -> [(String, SExpr)] -> SExpr
recordExpr at fields = Located at (SERecord [(Located at (SCName name), value) | (name, value) <- fields] False)

wildRowKind :: Span -> SKind -> SCon
wildRowKind at elementKind = Located at (SCWild (Located at (SKRecord elementKind)))

consumeLocatedCon :: SConF -> Parser SCon
consumeLocatedCon value = do
  token <- consumeToken
  pure (Located (tokenSpan token) value)
