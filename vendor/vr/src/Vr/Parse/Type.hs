{-# LANGUAGE DerivingStrategies #-}

module Vr.Parse.Type
  ( ConBinder (..)
  , wrapConBinder
  , parseKind
  , parseCon
  , parseConTerm
  , parseConProduct
  , parseRowLabel
  , parseOptionalKind
  ) where

import Vr.Parse.Core
import Vr.Parse.Lexer
import Vr.Source
data ConBinder
  = ConBinder !String !(Maybe SKind)
  | ConTupleBinder ![ConBinder]

wrapConBinder :: Span -> ConBinder -> (SCon, SKind) -> (SCon, SKind)
wrapConBinder at (ConBinder name maybeKind) (body, resultKind) =
  let kind = maybe (Located at SKWild) id maybeKind
   in ( Located at (SCAbs name maybeKind body)
      , Located at (SKArrow kind resultKind)
      )
wrapConBinder at (ConTupleBinder binders) (body, resultKind) =
  case binders of
    [] -> (body, resultKind)
    [ConBinder name maybeKind] ->
      let kind = maybe (Located at SKWild) id maybeKind
       in ( Located at (SCAbs name (Just kind) body)
          , Located at (SKArrow kind resultKind)
          )
    _ ->
      let components = [(name, maybe (Located at SKWild) id maybeKind) | ConBinder name maybeKind <- binders]
          tupleKind = Located at (SKTuple (map snd components))
          abstracted = foldr (\(name, kind) result -> Located at (SCAbs name (Just kind) result)) body components
          tuple = Located at (SCVar [] "$x")
          applied = foldl (\function (index, _) -> Located at (SCApp function (Located at (SCProj tuple index)))) abstracted (zip [1 ..] components)
       in ( Located at (SCAbs "$x" (Just tupleKind) applied)
          , Located at (SKArrow tupleKind resultKind)
          )

parseOptionalKind :: Parser (Maybe SKind)
parseOptionalKind = do
  next <- peekText
  case next of
    Just "::" -> expectText "::" *> (Just <$> parseKind)
    Just "::_" -> do
      token <- expectText "::_"
      pure (Just (Located (tokenSpan token) SKWild))
    _ -> pure Nothing
parseKind :: Parser SKind
parseKind = parseKindArrow

parseKindArrow :: Parser SKind
parseKindArrow = do
  left <- parseKindAtom
  arrow <- acceptText "->"
  if arrow
    then do
      right <- parseKindArrow
      pure (Located (mergeSpans (locatedSpan left) (locatedSpan right)) (SKArrow left right))
    else pure left

parseKindAtom :: Parser SKind
parseKindAtom = do
  next <- peekKind
  case next of
    Just (TokenConstructor name) -> do
      token <- consumeToken
      kindArrow <- acceptText "-->"
      if kindArrow
        then do
          body <- parseKind
          pure (Located (mergeSpans (tokenSpan token) (locatedSpan body)) (SKFun name body))
        else pure (Located (tokenSpan token) (builtinKind name))
    Just (TokenPunctuation "__") -> do
      token <- consumeToken
      pure (Located (tokenSpan token) SKWild)
    Just (TokenPunctuation "{") -> do
      start <- consumeToken
      element <- parseKind
      end <- expectText "}"
      pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SKRecord element))
    Just (TokenPunctuation "(") -> do
      start <- consumeToken
      first <- parseKind
      tuple <- acceptText "*"
      if tuple
        then do
          rest <- parseKindTupleTail
          end <- expectText ")"
          pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SKTuple (first : rest)))
        else do
          end <- expectText ")"
          pure first {locatedSpan = mergeSpans (tokenSpan start) (tokenSpan end)}
    _ -> parseFailure "kind" "Expected a kind"

parseKindTupleTail :: Parser [SKind]
parseKindTupleTail = do
  next <- parseKind
  more <- acceptText "*"
  if more then (next :) <$> parseKindTupleTail else pure [next]

builtinKind :: String -> SKindF
builtinKind name = case name of
  "Type" -> SKType
  "Name" -> SKName
  "Unit" -> SKUnit
  _ -> SKVar name

parseCon :: Parser SCon
parseCon = parseConFunction

parseConFunction :: Parser SCon
parseConFunction = do
  kindBinder <- kindConBinderAhead
  case kindBinder of
    Just (name, token) -> do
      _ <- consumeToken
      _ <- expectText "==>"
      body <- parseConFunction
      pure (Located (mergeSpans (tokenSpan token) (locatedSpan body)) (SCKAbs name body))
    Nothing -> parseAfterKindBinder
  where
    parseAfterKindBinder = do
      guardAhead <- disjointGuardAhead
      if guardAhead
        then do
          start <- expectText "["
          left <- parseCon
          _ <- expectText "~"
          right <- parseCon
          _ <- expectText "]"
          _ <- expectText "=>"
          body <- parseConFunction
          pure (Located (mergeSpans (tokenSpan start) (locatedSpan body)) (SCTDisjoint left right body))
        else parseAfterGuard
    parseAfterGuard = do
      binder <- conFunctionBinderAhead
      case binder of
        Just (name, explicitness, token) -> do
          _ <- consumeToken
          _ <- consumeToken
          kind <- parseBinderKind
          _ <- expectText "->"
          body <- parseConFunction
          pure (Located (mergeSpans (tokenSpan token) (locatedSpan body)) (SCTCFun explicitness name kind body))
        Nothing -> do
          left <- parseConConcat
          arrow <- acceptText "->"
          if arrow
            then do
              right <- parseConFunction
              pure (Located (mergeSpans (locatedSpan left) (locatedSpan right)) (SCTFun left right))
            else pure left

kindConBinderAhead :: Parser (Maybe (String, Token))
kindConBinderAhead = do
  first <- peekToken
  second <- peekTextN 1
  pure $ case (first, second) of
    (Just token@(Token _ (TokenConstructor name)), Just "==>") -> Just (name, token)
    _ -> Nothing

conFunctionBinderAhead :: Parser (Maybe (String, Explicitness, Token))
conFunctionBinderAhead = do
  first <- peekToken
  second <- peekKindN 1
  pure $ case (first, second) of
    (Just token@(Token _ (TokenIdentifier name)), Just (TokenPunctuation "::")) -> Just (name, Explicit, token)
    (Just token@(Token _ (TokenIdentifier name)), Just (TokenPunctuation ":::")) -> Just (name, Implicit, token)
    _ -> Nothing

-- In a constructor-polymorphic function, the following '->' terminates the
-- binder.  Arrow kinds at this position are parenthesized in Ur source; parsing
-- a full kind here would greedily consume the function-type arrow itself.
parseBinderKind :: Parser SKind
parseBinderKind = parseKindAtom

parseConConcat :: Parser SCon
parseConConcat = do
  left <- parseConProduct
  concatenated <- acceptText "++"
  if concatenated
    then do
      right <- parseConConcat
      pure (Located (mergeSpans (locatedSpan left) (locatedSpan right)) (SCConcat left right))
    else pure left

parseConProduct :: Parser SCon
parseConProduct = do
  first <- parseConApplication
  productOperator <- acceptText "*"
  if not productOperator
    then pure first
    else do
      rest <- parseStarTail parseConApplication
      let constructors = first : rest
          at = mergeSpans (locatedSpan first) (locatedSpan (last constructors))
      pure (tupleType at constructors)

parseConApplication :: Parser SCon
parseConApplication = do
  first <- parseConTerm
  parseMore first
  where
    parseMore function = do
      next <- peekKind
      if maybe False startsConTerm next
        then do
          argument <- parseConTerm
          parseMore (Located (mergeSpans (locatedSpan function) (locatedSpan argument)) (SCApp function argument))
        else pure function

parseConTerm :: Parser SCon
parseConTerm = do
  next <- peekKind
  base <- case next of
    Just (TokenIdentifier _) -> do
      path <- parseValuePath
      pure (Located (pathSpan path) (pathToCon path))
    Just (TokenConstructor _) -> do
      first <- peekToken
      second <- peekTextN 1
      case (first, second) of
        (Just token@(Token _ (TokenConstructor name)), Just "-->") -> do
          _ <- consumeToken
          _ <- expectText "-->"
          body <- parseCon
          pure (Located (mergeSpans (tokenSpan token) (locatedSpan body)) (SCTKFun name body))
        _ -> do
          path <- parseValuePath
          pure (Located (pathSpan path) (pathToCon path))
    Just (TokenPunctuation "(") -> parseParenthesizedCon
    Just (TokenPunctuation "[") -> parseRowCon
    Just (TokenPunctuation "{") -> parseRecordTypeCon
    Just (TokenPunctuation "$") -> do
      start <- consumeToken
      row <- parseConTerm
      pure (Located (mergeSpans (tokenSpan start) (locatedSpan row)) (SCTRecord row))
    Just (TokenPunctuation "#") -> do
      start <- consumeToken
      name <- expectNameConstant
      pure (Located (mergeSpans (tokenSpan start) (snd name)) (SCName (fst name)))
    Just (TokenPunctuation "_") -> do
      token <- consumeToken
      annotated <- acceptText "::"
      kind <- if annotated then parseKind else pure (Located (tokenSpan token) SKWild)
      pure (Located (mergeSpans (tokenSpan token) (locatedSpan kind)) (SCWild kind))
    Just (TokenKeyword "map") -> do
      token <- consumeToken
      pure (Located (tokenSpan token) SCMap)
    Just TokenUnit -> do
      token <- consumeToken
      pure (Located (tokenSpan token) SCUnit)
    Just (TokenKeyword "fn") -> parseConLambda
    _ -> parseFailure "constructor" "Expected a constructor or type"
  parseConProjection base

parseParenthesizedCon :: Parser SCon
parseParenthesizedCon = do
  start <- expectText "("
  first <- parseCon
  next <- peekText
  case next of
    Just "," -> do
      _ <- expectText ","
      rest <- parseCommaTail parseCon
      end <- expectText ")"
      pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SCTuple (first : rest)))
    Just "*" -> do
      _ <- expectText "*"
      rest <- parseStarTail parseConApplication
      end <- expectText ")"
      pure (tupleType (mergeSpans (tokenSpan start) (tokenSpan end)) (first : rest))
    Just ")" -> do
      end <- expectText ")"
      annotation <- acceptText "::"
      if annotation
        then do
          kind <- parseKind
          pure (Located (mergeSpans (tokenSpan start) (locatedSpan kind)) (SCAnnot first kind))
        else pure first {locatedSpan = mergeSpans (tokenSpan start) (tokenSpan end)}
    _ -> parseFailure "constructor-parenthesis" "Expected ',', '*', or ')' in constructor"

parseRowCon :: Parser SCon
parseRowCon = do
  start <- expectText "["
  empty <- acceptText "]"
  if empty
    then pure (Located (tokenSpan start) (SCRecord []))
    else do
      firstName <- parseRowLabel
      next <- peekText
      case next of
        Just "~" -> do
          _ <- expectText "~"
          right <- parseCon
          _ <- expectText "]"
          _ <- expectText "=>"
          body <- parseCon
          pure (Located (mergeSpans (tokenSpan start) (locatedSpan body)) (SCTDisjoint firstName right body))
        _ -> do
          fields <- case next of
            Just "=" -> do
              _ <- expectText "="
              value <- parseCon
              rest <- parseMoreRowFields "="
              pure ((firstName, value) : rest)
            Just "," -> do
              let unit = Located (locatedSpan firstName) SCUnit
              _ <- expectText ","
              restNames <- parseUnitRowTail
              pure ((firstName, unit) : restNames)
            Just "]" -> pure [(firstName, Located (locatedSpan firstName) SCUnit)]
            _ -> parseFailure "row" "Expected '=', ',', or ']' in row"
          end <- expectText "]"
          pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SCRecord fields))

parseMoreRowFields :: String -> Parser [(SCon, SCon)]
parseMoreRowFields separator = do
  comma <- acceptText ","
  if not comma
    then pure []
    else do
      done <- atText "]"
      if done
        then pure []
        else do
          name <- parseRowLabel
          _ <- expectText separator
          value <- parseCon
          ((name, value) :) <$> parseMoreRowFields separator

parseUnitRowTail :: Parser [(SCon, SCon)]
parseUnitRowTail = do
  name <- parseRowLabel
  let pair = (name, Located (locatedSpan name) SCUnit)
  more <- acceptText ","
  if more
    then do
      done <- atText "]"
      if done then pure [pair] else (pair :) <$> parseUnitRowTail
    else pure [pair]

parseRecordTypeCon :: Parser SCon
parseRecordTypeCon = do
  start <- expectText "{"
  empty <- acceptText "}"
  if empty
    then do
      let at = tokenSpan start
      pure (Located at (SCTRecord (Located at (SCRecord []))))
    else do
      name <- parseRowLabel
      _ <- expectText ":"
      value <- parseCon
      rest <- parseMoreRecordTypeFields
      end <- expectText "}"
      let at = mergeSpans (tokenSpan start) (tokenSpan end)
      pure (Located at (SCTRecord (Located at (SCRecord ((name, value) : rest)))))

parseMoreRecordTypeFields :: Parser [(SCon, SCon)]
parseMoreRecordTypeFields = do
  comma <- acceptText ","
  if not comma
    then pure []
    else do
      end <- atText "}"
      if end
        then pure []
        else do
          name <- parseRowLabel
          _ <- expectText ":"
          value <- parseCon
          ((name, value) :) <$> parseMoreRecordTypeFields

parseConLambda :: Parser SCon
parseConLambda = do
  start <- expectText "fn"
  binders <- parseLambdaConBinders
  _ <- expectText "=>"
  body <- parseCon
  let at = mergeSpans (tokenSpan start) (locatedSpan body)
  pure (fst (foldr (wrapConBinder at) (body, Located at SKWild) binders))

parseLambdaConBinders :: Parser [ConBinder]
parseLambdaConBinders = do
  next <- peekKind
  case next of
    Just (TokenIdentifier name) -> do
      _ <- consumeToken
      kind <- parseOptionalKind
      (ConBinder name kind :) <$> parseLambdaConBinders
    Just (TokenPunctuation "_") -> do
      _ <- consumeToken
      kind <- parseOptionalKind
      (ConBinder "_" kind :) <$> parseLambdaConBinders
    Just (TokenPunctuation "(") -> do
      _ <- consumeToken
      group <- parseLambdaConBinderGroup
      _ <- expectText ")"
      rest <- parseLambdaConBinders
      pure (ConTupleBinder group : rest)
    _ -> pure []

parseLambdaConBinderGroup :: Parser [ConBinder]
parseLambdaConBinderGroup = do
  (name, _) <- expectIdentifier
  kind <- parseOptionalKind
  more <- acceptText ","
  if more
    then (ConBinder name kind :) <$> parseLambdaConBinderGroup
    else pure [ConBinder name kind]

parseConProjection :: SCon -> Parser SCon
parseConProjection constructor = do
  dot <- acceptText "."
  if not dot
    then pure constructor
    else do
      (index, token) <- expectInteger
      let projected = Located (mergeSpans (locatedSpan constructor) (tokenSpan token)) (SCProj constructor (fromIntegral index))
      parseConProjection projected

parseRowLabel :: Parser SCon
parseRowLabel = do
  next <- peekKind
  case next of
    Just (TokenConstructor name) -> do
      token <- consumeToken
      dotted <- atText "."
      if dotted
        then do
          putBack token
          path <- parseValuePath
          pure (Located (pathSpan path) (pathToCon path))
        else pure (Located (tokenSpan token) (SCName name))
    Just (TokenIdentifier _) -> do
      path <- parseValuePath
      pure (Located (pathSpan path) (pathToCon path))
    Just (TokenInt value) -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SCName (show value)))
    _ -> parseFailure "row-label" "Expected a row label"
