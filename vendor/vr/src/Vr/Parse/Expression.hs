{-# LANGUAGE DerivingStrategies #-}

module Vr.Parse.Expression
  ( LambdaArgument (..)
  , parseExpr
  , parseExprApplications
  , parseExprTerm
  , parseLambdaArguments
  , wrapLambdaArgument
  , parseValueDefinitions
  , expressionSpanOfDefinition
  , parseValueArguments
  , wrapValueArgument
  , lambdaArgumentType
  , patternAnnotation
  , patternType
  , parseOptionalTypeAnnotation
  ) where

import Control.Monad (unless)
import Vr.Parse.CSS (desugarSpecialApplication)
import Vr.Parse.Core
import Vr.Parse.Expression.SQL
import Vr.Parse.Expression.XML
import Vr.Parse.Lexer
import Vr.Parse.Pattern
import Vr.Parse.Type
import Vr.Source
parseValueDefinitions :: Parser [(String, Maybe SCon, SExpr)]
parseValueDefinitions = do
  first <- parseValueDefinition
  rest <- parseSeparated "and" parseValueDefinition
  pure (first : rest)

parseValueDefinition :: Parser (String, Maybe SCon, SExpr)
parseValueDefinition = do
  (name, nameToken) <- expectIdentifier
  arguments <- parseValueArguments
  resultType <- parseOptionalTypeAnnotation
  _ <- expectText "="
  body <- parseExpr
  let at = mergeSpans (tokenSpan nameToken) (locatedSpan body)
      fullType = foldr (lambdaArgumentType at) <$> resultType <*> pure arguments
  pure (name, fullType, foldr (wrapLambdaArgument at) body arguments)

expressionSpanOfDefinition :: (String, Maybe SCon, SExpr) -> Span
expressionSpanOfDefinition (_, _, expression) = locatedSpan expression

parseValueArguments :: Parser [LambdaArgument]
parseValueArguments = parseLambdaArguments False

wrapValueArgument :: Span -> SPattern -> SExpr -> SExpr
wrapValueArgument at pattern' body = case locatedValue pattern' of
  SPVar name -> Located at (SEAbs name (patternAnnotation pattern') body)
  _ ->
    let temporary = "$x"
        variable = Located at (SEVar [] temporary DontInfer)
        matched = Located at (SECase variable [(pattern', body)])
     in Located at (SEAbs temporary (Just (patternType at pattern')) matched)

lambdaArgumentType :: Span -> LambdaArgument -> SCon -> SCon
lambdaArgumentType at argument result = case argument of
  LambdaPattern pattern' ->
    Located (mergeSpans (locatedSpan pattern') (locatedSpan result)) (SCTFun (patternType (locatedSpan pattern') pattern') result)
  LambdaCon explicitness name kind -> Located at (SCTCFun explicitness name kind result)
  LambdaKind name -> Located at (SCTKFun name result)
  LambdaDisjoint left right -> Located at (SCTDisjoint left right result)

patternAnnotation :: SPattern -> Maybe SCon
patternAnnotation pattern' = case locatedValue pattern' of
  SPAnnot _ annotation -> Just annotation
  _ -> Nothing

patternType :: Span -> SPattern -> SCon
patternType at pattern' = maybe (wildType at) id (patternAnnotation pattern')

parseOptionalTypeAnnotation :: Parser (Maybe SCon)
parseOptionalTypeAnnotation = do
  hasAnnotation <- acceptText ":"
  if hasAnnotation then Just <$> parseCon else pure Nothing

parseExpr :: Parser SExpr
parseExpr = do
  left <- parseExprPrecedence 0
  next <- peekText
  case next of
    Just "<-" -> do
      _ <- expectText "<-"
      action <- parseExprApplications
      _ <- expectText ";"
      continuation <- parseExpr
      pattern' <- expressionToPattern left
      let at = mergeSpans (locatedSpan left) (locatedSpan continuation)
      pure (bindExpression at pattern' Nothing action continuation)
    Just ";" -> do
      _ <- expectText ";"
      continuation <- parseExpr
      let at = mergeSpans (locatedSpan left) (locatedSpan continuation)
          pattern' = Located at (SPVar "_")
          unitType = Located at (SCTRecord (Located at (SCRecord [])))
      pure (bindExpression at pattern' (Just unitType) left continuation)
    _ -> pure (desugarSpecialApplication left)

parseExprPrecedence :: Int -> Parser SExpr
parseExprPrecedence threshold = do
  left <- parseExprPrefix
  parseExprInfix threshold left

parseExprPrefix :: Parser SExpr
parseExprPrefix = do
  next <- peekText
  case next of
    Just "fn" -> parseExpressionLambda
    Just "case" -> parseCaseExpression
    Just "if" -> parseIfExpression
    Just "let" -> parseLetExpression
    Just "-" -> do
      start <- expectText "-"
      argument <- parseExprTerm
      pure (basisUnary (mergeSpans (tokenSpan start) (locatedSpan argument)) "neg" argument)
    _ -> parseExprApplications

parseExprApplications :: Parser SExpr
parseExprApplications = do
  first <- parseExprTerm
  parseMore first
  where
    parseMore function = do
      next <- peekKind
      case next of
        Just (TokenPunctuation "[") -> do
          closesImmediately <- (== Just "]") <$> peekTextN 1
          if closesImmediately
            then do
              argument <- parseExprTerm
              parseMore (Located (mergeSpans (locatedSpan function) (locatedSpan argument)) (SEApp function argument))
            else do
              _ <- expectText "["
              constructor <- parseCon
              end <- expectText "]"
              parseMore (Located (mergeSpans (locatedSpan function) (tokenSpan end)) (SECApp function constructor))
        Just (TokenPunctuation "!") -> do
          token <- consumeToken
          parseMore (Located (mergeSpans (locatedSpan function) (tokenSpan token)) (SEDisjointApp function))
        kind | maybe False startsExprTerm kind -> do
          argument <- parseExprTerm
          parseMore (Located (mergeSpans (locatedSpan function) (locatedSpan argument)) (SEApp function argument))
        _ -> pure function

parseExprTerm :: Parser SExpr
parseExprTerm = do
  next <- peekKind
  base <- case next of
    Just (TokenInt value) -> primitive (PrimInt value)
    Just (TokenFloat value) -> primitive (PrimFloat value)
    Just (TokenString value) -> primitive (PrimString NormalString value)
    Just (TokenChar value) -> primitive (PrimChar value)
    Just TokenUnit -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SERecord [] False))
    Just (TokenIdentifier _) -> valuePathExpression Infer
    Just (TokenConstructor _) -> valuePathExpression Infer
    Just (TokenPunctuation "@") -> do
      start <- consumeToken
      twice <- acceptText "@"
      expression <- valuePathExpression (if twice then DontInfer else TypesOnly)
      pure expression {locatedSpan = mergeSpans (tokenSpan start) (locatedSpan expression)}
    Just (TokenPunctuation "_") -> do
      token <- consumeToken
      pure (Located (tokenSpan token) SEWild)
    Just (TokenPunctuation "(") -> parseParenthesizedExpr
    Just (TokenPunctuation "{") -> parseRecordExpr
    Just (TokenPunctuation "[") -> do
      start <- consumeToken
      end <- expectText "]"
      pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SEVar ["Basis"] "Nil" Infer))
    Just (TokenXmlBegin tag) -> parseXmlRoot tag
    Just (TokenXmlBeginEnd tag) -> do
      token <- consumeToken
      unless (tag == "xml")
        (parseFailureAt (tokenSpan token) "xml-root" "Initial XML tag pair must both be tagged <xml>")
      pure (emptyXml (tokenSpan token))
    _ -> parseFailure "expression" "Expected an expression"
  parseExpressionProjection base
  where
    primitive value = do
      token <- consumeToken
      pure (Located (tokenSpan token) (SEPrim value))

parseExpressionProjection :: SExpr -> Parser SExpr
parseExpressionProjection expression = do
  dot <- acceptText "."
  if not dot
    then pure expression
    else do
      field <- parseProjectionLabel
      let projected = Located (mergeSpans (locatedSpan expression) (locatedSpan field)) (SEField expression field)
      parseExpressionProjection projected

parseProjectionLabel :: Parser SCon
parseProjectionLabel = do
  next <- peekKind
  case next of
    Just (TokenConstructor name) -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SCName name))
    Just (TokenIdentifier name) -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SCVar [] name))
    Just (TokenInt value) -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SCName (show value)))
    _ -> parseFailure "field" "Expected a field label"

parseExprInfix :: Int -> SExpr -> Parser SExpr
parseExprInfix threshold left = do
  next <- peekKind
  case next >>= expressionOperator of
    Just operator | operatorPrecedence operator >= threshold -> do
      token <- consumeToken
      let rightMinimum = operatorPrecedence operator + if operatorRightAssociative operator then 0 else 1
      case operator of
        ExprAnnot -> do
          constructor <- parseCon
          parseExprInfix threshold (Located (mergeSpans (locatedSpan left) (locatedSpan constructor)) (SEAnnot left constructor))
        ExprCut -> do
          constructor <- parseConProduct
          parseExprInfix threshold (Located (mergeSpans (locatedSpan left) (locatedSpan constructor)) (SECut left constructor))
        ExprCutMulti -> do
          constructor <- parseConProduct
          parseExprInfix threshold (Located (mergeSpans (locatedSpan left) (locatedSpan constructor)) (SECutMulti left constructor))
        _ -> do
          right <- parseExprPrecedence rightMinimum
          let at = mergeSpans (locatedSpan left) (locatedSpan right)
          parseExprInfix threshold (desugarExpressionOperator at token operator left right)
    _ -> pure left

data ExprOperator
  = ExprAnnot | ExprOr | ExprAnd | ExprEq | ExprNe | ExprLt | ExprLe | ExprGt | ExprGe
  | ExprForward | ExprReverse | ExprCompose | ExprAndThen | ExprConcat | ExprStringConcat
  | ExprCut | ExprCutMulti | ExprPlus | ExprMinus | ExprTimes | ExprDivide | ExprMod | ExprCons
  deriving stock (Eq, Show)

expressionOperator :: TokenKind -> Maybe ExprOperator
expressionOperator token = case token of
  TokenPunctuation ":" -> Just ExprAnnot
  TokenPunctuation "||" -> Just ExprOr
  TokenPunctuation "&&" -> Just ExprAnd
  TokenPunctuation "=" -> Just ExprEq
  TokenPunctuation "<>" -> Just ExprNe
  TokenPunctuation "<" -> Just ExprLt
  TokenPunctuation "<=" -> Just ExprLe
  TokenPunctuation ">" -> Just ExprGt
  TokenPunctuation ">=" -> Just ExprGe
  TokenPunctuation "<|" -> Just ExprForward
  TokenPunctuation "|>" -> Just ExprReverse
  TokenPunctuation "<<<" -> Just ExprCompose
  TokenPunctuation ">>>" -> Just ExprAndThen
  TokenPunctuation "++" -> Just ExprConcat
  TokenPunctuation "^" -> Just ExprStringConcat
  TokenPunctuation "--" -> Just ExprCut
  TokenPunctuation "---" -> Just ExprCutMulti
  TokenPunctuation "+" -> Just ExprPlus
  TokenPunctuation "-" -> Just ExprMinus
  TokenPunctuation "*" -> Just ExprTimes
  TokenPunctuation "/" -> Just ExprDivide
  TokenPunctuation "%" -> Just ExprMod
  TokenPunctuation "::" -> Just ExprCons
  _ -> Nothing

operatorPrecedence :: ExprOperator -> Int
operatorPrecedence operator = case operator of
  ExprOr -> 20
  ExprAnd -> 30
  ExprAnnot -> 40
  ExprEq -> 50
  ExprNe -> 50
  ExprLt -> 50
  ExprLe -> 50
  ExprGt -> 50
  ExprGe -> 50
  ExprForward -> 60
  ExprReverse -> 60
  ExprCompose -> 70
  ExprAndThen -> 70
  ExprConcat -> 80
  ExprStringConcat -> 80
  ExprCut -> 90
  ExprCutMulti -> 90
  ExprPlus -> 100
  ExprMinus -> 100
  ExprTimes -> 110
  ExprDivide -> 110
  ExprMod -> 110
  ExprCons -> 35

operatorRightAssociative :: ExprOperator -> Bool
operatorRightAssociative operator = operator `elem` [ExprForward, ExprCompose, ExprAndThen, ExprConcat, ExprStringConcat, ExprCons]

desugarExpressionOperator :: Span -> Token -> ExprOperator -> SExpr -> SExpr -> SExpr
desugarExpressionOperator at _ operator left right = case operator of
  ExprEq -> basisBinary at "eq" left right
  ExprNe -> basisBinary at "ne" left right
  ExprLt -> basisBinary at "lt" left right
  ExprLe -> basisBinary at "le" left right
  ExprGt -> basisBinary at "gt" left right
  ExprGe -> basisBinary at "ge" left right
  ExprPlus -> basisBinary at "plus" left right
  ExprMinus -> basisBinary at "minus" left right
  ExprTimes -> basisBinary at "times" left right
  ExprDivide -> basisBinary at "divide" left right
  ExprMod -> basisBinary at "mod" left right
  ExprStringConcat -> basisBinary at "strcat" left right
  ExprConcat -> Located at (SEConcat left right)
  ExprForward -> Located at (SEApp left right)
  ExprReverse -> Located at (SEApp right left)
  ExprCompose -> topBinary at "compose" left right
  ExprAndThen -> topBinary at "compose" right left
  ExprAnd ->
    Located at (SECase left [(basisPattern at "True", right), (basisPattern at "False", basisVar at "False")])
  ExprOr ->
    Located at (SECase left [(basisPattern at "True", basisVar at "True"), (basisPattern at "False", right)])
  ExprCons ->
    let tuple = Located at (SERecord [(Located at (SCName "1"), left), (Located at (SCName "2"), right)] False)
     in Located at (SEApp (basisVar at "Cons") tuple)
  ExprAnnot -> left
  ExprCut -> left
  ExprCutMulti -> left

parseExpressionLambda :: Parser SExpr
parseExpressionLambda = do
  start <- expectText "fn"
  arguments <- parseLambdaArguments True
  _ <- expectText "=>"
  body <- parseExpr
  let at = mergeSpans (tokenSpan start) (locatedSpan body)
  pure (foldr (wrapLambdaArgument at) body arguments)

data LambdaArgument
  = LambdaPattern !SPattern
  | LambdaCon !Explicitness !String !SKind
  | LambdaKind !String
  | LambdaDisjoint !SCon !SCon

parseLambdaArguments :: Bool -> Parser [LambdaArgument]
parseLambdaArguments allowArgumentAnnotation = do
  next <- peekKind
  case next of
    Just (TokenPunctuation "[") -> do
      guardArgument <- disjointGuardAhead
      argument <- if guardArgument
        then do
          _ <- expectText "["
          left <- parseCon
          _ <- expectText "~"
          right <- parseCon
          _ <- expectText "]"
          pure (LambdaDisjoint left right)
        else do
          start <- consumeToken
          first <- peekKind
          case first of
            Just (TokenConstructor kindName) -> do
              _ <- consumeToken
              _ <- expectText "]"
              pure (LambdaKind kindName)
            Just (TokenIdentifier name) -> do
              _ <- consumeToken
              punctuation' <- peekText
              explicitness <- case punctuation' of
                Just ":::" -> consumeToken *> pure Implicit
                Just "::" -> consumeToken *> pure Explicit
                Just ":::_" -> consumeToken *> pure Implicit
                Just "::_" -> consumeToken *> pure Explicit
                _ -> pure Implicit
              kind <- if punctuation' `elem` [Just "::", Just ":::"] then parseKind else pure (Located (tokenSpan start) SKWild)
              _ <- expectText "]"
              pure (LambdaCon explicitness name kind)
            _ -> parseFailure "lambda-argument" "Invalid bracketed lambda argument"
      (argument :) <$> parseLambdaArguments allowArgumentAnnotation
    kind | maybe False startsPatternTerm kind -> do
      pattern' <- if allowArgumentAnnotation then parsePattern else parseLambdaPattern
      (LambdaPattern pattern' :) <$> parseLambdaArguments allowArgumentAnnotation
    _ -> pure []

-- A colon following a complete function argument is the function's result
-- annotation.  Argument annotations remain unambiguous inside parentheses,
-- as in @(x : t)@.  Parsing a full pattern here would greedily turn
-- @fun f (x : a) : b = ...@ into a doubly annotated argument and lose @b@.
parseLambdaPattern :: Parser SPattern
parseLambdaPattern = do
  first <- parsePatternTerm
  cons <- acceptText "::"
  if cons
    then do
      rest <- parsePattern
      let at = mergeSpans (locatedSpan first) (locatedSpan rest)
          payload = Located at (SPRecord [("1", first), ("2", rest)] False)
      pure (Located at (SPCon ["Basis"] "Cons" (Just payload)))
    else pure first

wrapLambdaArgument :: Span -> LambdaArgument -> SExpr -> SExpr
wrapLambdaArgument at argument body = case argument of
  LambdaPattern pattern' -> wrapValueArgument at pattern' body
  LambdaCon explicitness name kind -> Located at (SECAbs explicitness name kind body)
  LambdaKind name -> Located at (SEKAbs name body)
  LambdaDisjoint left right -> Located at (SEDisjoint left right body)

bindExpression :: Span -> SPattern -> Maybe SCon -> SExpr -> SExpr -> SExpr
bindExpression at pattern' annotation action continuation =
  let binder = case locatedValue pattern' of
        SPVar name -> Located at (SEAbs name annotation continuation)
        _ ->
          let temporary = "$x"
              variable = Located at (SEVar [] temporary DontInfer)
              matched = Located at (SECase variable [(pattern', continuation)])
           in Located at (SEAbs temporary annotation matched)
   in Located at (SEApp (Located at (SEApp (basisVar at "bind") action)) binder)

expressionToPattern :: SExpr -> Parser SPattern
expressionToPattern expression = case locatedValue expression of
  SEWild -> pure (Located (locatedSpan expression) (SPVar "_"))
  SEVar modules name _
    | startsWithUpper name -> pure (Located (locatedSpan expression) (SPCon modules name Nothing))
    | otherwise -> pure (Located (locatedSpan expression) (SPVar name))
  SEPrim primitive -> pure (Located (locatedSpan expression) (SPPrim primitive))
  SEApp function argument -> case locatedValue function of
    SEVar modules name _ | startsWithUpper name -> do
      argumentPattern <- expressionToPattern argument
      pure (Located (locatedSpan expression) (SPCon modules name (Just argumentPattern)))
    _ -> notPattern
  SERecord fields flexible -> do
    patternFields <- mapM fieldPattern fields
    pure (Located (locatedSpan expression) (SPRecord patternFields flexible))
  SEAnnot inner valueType -> do
    pattern' <- expressionToPattern inner
    pure (Located (locatedSpan expression) (SPAnnot pattern' valueType))
  _ -> notPattern
  where
    fieldPattern (name, value) = do
      fieldName <- conLabelName name
      valuePattern <- expressionToPattern value
      pure (fieldName, valuePattern)
    notPattern = parseFailureAt (locatedSpan expression) "expression-pattern" "This is an expression but not a pattern"

conLabelName :: SCon -> Parser String
conLabelName constructor = case locatedValue constructor of
  SCName name -> pure name
  SCVar [] name -> pure name
  _ -> parseFailureAt (locatedSpan constructor) "pattern-field" "Record pattern has a non-name field"

startsWithUpper :: String -> Bool
startsWithUpper (first : _) = first >= 'A' && first <= 'Z'
startsWithUpper [] = False

parseCaseExpression :: Parser SExpr
parseCaseExpression = do
  start <- expectText "case"
  scrutinee <- parseExpr
  _ <- expectText "of"
  _ <- acceptText "|"
  first <- parseCaseBranch
  rest <- parseSeparated "|" parseCaseBranch
  let branches = first : rest
      endAt = locatedSpan (snd (last branches))
  pure (Located (mergeSpans (tokenSpan start) endAt) (SECase scrutinee branches))

parseCaseBranch :: Parser (SPattern, SExpr)
parseCaseBranch = do
  pattern' <- parsePattern
  _ <- expectText "=>"
  expression <- parseExpr
  pure (pattern', expression)

parseIfExpression :: Parser SExpr
parseIfExpression = do
  start <- expectText "if"
  condition <- parseExpr
  _ <- expectText "then"
  whenTrue <- parseExpr
  _ <- expectText "else"
  whenFalse <- parseExpr
  let at = mergeSpans (tokenSpan start) (locatedSpan whenFalse)
  pure (Located at (SECase condition [(basisPattern at "True", whenTrue), (basisPattern at "False", whenFalse)]))

parseLetExpression :: Parser SExpr
parseLetExpression = do
  start <- expectText "let"
  next <- peekText
  if next `elem` [Just "val", Just "fun"]
    then do
      declarations <- parseExpressionDeclarationsUntil ["in"]
      _ <- expectText "in"
      body <- parseExpr
      end <- expectText "end"
      pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SELet declarations body))
    else do
      body <- parseExpr
      _ <- expectText "where"
      declarations <- parseExpressionDeclarationsUntil ["end"]
      end <- expectText "end"
      pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SELet declarations body))

parseExpressionDeclarationsUntil :: [String] -> Parser [SEDecl]
parseExpressionDeclarationsUntil terminators = do
  stopped <- atAny terminators
  if stopped
    then pure []
    else do
      declaration <- parseExpressionDeclaration
      rest <- parseExpressionDeclarationsUntil terminators
      pure (declaration : rest)

parseExpressionDeclaration :: Parser SEDecl
parseExpressionDeclaration = do
  next <- peekText
  case next of
    Just "val" -> do
      start <- expectText "val"
      recursive <- acceptText "rec"
      if recursive
        then do
          definitions <- parseValueDefinitions
          pure (Located (mergeSpans (tokenSpan start) (expressionSpanOfDefinition (last definitions))) (SEDValRec definitions))
        else do
          pattern' <- parsePattern
          _ <- expectText "="
          expression <- parseExpr
          pure (Located (mergeSpans (tokenSpan start) (locatedSpan expression)) (SEDVal pattern' expression))
    Just "fun" -> do
      start <- expectText "fun"
      definitions <- parseValueDefinitions
      pure (Located (mergeSpans (tokenSpan start) (expressionSpanOfDefinition (last definitions))) (SEDValRec definitions))
    _ -> parseFailure "expression-declaration" "Expected val or fun"

parseParenthesizedExpr :: Parser SExpr
parseParenthesizedExpr = do
  start <- expectText "("
  next <- peekText
  case next of
    Just "SELECT" -> finishSql start =<< parseSqlQuery
    Just "SELECT1" -> expectText "SELECT1" *> (finishSql start =<< parseSqlQuery1)
    Just "SQL" -> expectText "SQL" *> (finishSql start =<< parseSqlExpr)
    Just "WHERE" -> expectText "WHERE" *> (finishSql start =<< parseSqlExpr)
    Just "FROM" -> do
      _ <- expectText "FROM"
      from <- parseSqlFrom
      finishSql start (sqlFromExpression from)
    Just "INSERT" -> finishSql start =<< parseSqlInsert
    Just "UPDATE" -> finishSql start =<< parseSqlUpdate
    Just "DELETE" -> finishSql start =<< parseSqlDelete
    _ -> do
      expression <- parseExpr
      comma <- acceptText ","
      if comma
        then do
          rest <- parseCommaTail parseExpr
          end <- expectText ")"
          let at = mergeSpans (tokenSpan start) (tokenSpan end)
              fields = zipWith (\index item -> (Located at (SCName (show index)), item)) [(1 :: Int) ..] (expression : rest)
          pure (Located at (SERecord fields False))
        else do
          end <- expectText ")"
          pure expression {locatedSpan = mergeSpans (tokenSpan start) (tokenSpan end)}

finishSql :: Token -> SExpr -> Parser SExpr
finishSql start expression = do
  end <- expectText ")"
  pure expression {locatedSpan = mergeSpans (tokenSpan start) (tokenSpan end)}
