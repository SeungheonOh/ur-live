{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Vr.Parse.Core
  ( Parser
  , runParser
  , ParsedPath (..)
  , parseValuePath
  , parseConstructorPath
  , parseModulePath
  , pathToCon
  , valuePathExpression
  , expectNameConstant
  , expectFieldName
  , parseWhileIdentifier
  , parseCommaTail
  , parseStarTail
  , parseSeparated
  , tupleType
  , wildType
  , entable
  , basisVar
  , topVar
  , basisUnary
  , basisBinary
  , topBinary
  , basisPattern
  , startsConTerm
  , startsExprTerm
  , startsPatternTerm
  , disjointGuardAhead
  , tokenKindMaybe
  , tokenText
  , peekToken
  , peekKind
  , peekKindN
  , peekText
  , peekTextN
  , atText
  , atAny
  , atEOF
  , consumeToken
  , putBack
  , expectText
  , expectOneOf
  , acceptText
  , expectIdentifier
  , expectConstructor
  , expectInteger
  , expectString
  , expectXmlEnd
  , expectEOF
  , parseFailure
  , parseFailureAt
  , ifM
  , listHead
  , lastMaybe
  , sndMaybe
  , atIndex
  , capitalize
  , asciiLower
  , foldSpans
  , optionalText
  , applyMany
  ) where

import qualified Data.ByteString as BS
import Control.Monad (when)
import Control.Monad.State.Strict (MonadState, StateT (..), evalStateT, get, gets, put)
import Data.Char (chr, ord)
import Data.Int (Int64)
import Vr.Parse.Lexer
import Vr.Source
newtype Parser value = Parser
  { unParser :: StateT [Token] (Either Diagnostic) value
  }
  deriving newtype (Functor, Applicative, Monad, MonadState [Token])

runParser :: Parser value -> [Token] -> Either Diagnostic value
runParser parser = evalStateT (unParser parser)

capitalize :: String -> String
capitalize [] = []
capitalize (first : rest)
  | first >= 'a' && first <= 'z' = chr (ord first - 32) : rest
  | otherwise = first : rest

asciiLower :: Char -> Char
asciiLower character
  | character >= 'A' && character <= 'Z' = chr (ord character + 32)
  | otherwise = character

foldSpans :: Span -> [Span] -> Span
foldSpans = foldl' mergeSpans

optionalText :: String -> Parser ()
optionalText text = acceptText text >> pure ()

applyMany :: Span -> SExpr -> [SExpr] -> SExpr
applyMany at = foldl' (\function argument -> Located at (SEApp function argument))

data ParsedPath = ParsedPath
  { pathPieces :: ![String]
  , pathSpan :: !Span
  }

parseValuePath :: Parser ParsedPath
parseValuePath = parseDottedPath True

parseConstructorPath :: Parser ParsedPath
parseConstructorPath = parseDottedPath False

parseModulePath :: Parser ParsedPath
parseModulePath = do
  (first, token) <- expectConstructor
  rest <- parseDottedConstructors
  let endAt = maybe (tokenSpan token) tokenSpan (sndMaybe rest)
  pure (ParsedPath (first : map fst rest) (mergeSpans (tokenSpan token) endAt))

parseDottedConstructors :: Parser [(String, Token)]
parseDottedConstructors = do
  dot <- atText "."
  if not dot
    then pure []
    else do
      next <- peekKindN 1
      case next of
        Just (TokenConstructor _) -> do
          _ <- expectText "."
          item <- expectConstructor
          (item :) <$> parseDottedConstructors
        _ -> pure []

parseDottedPath :: Bool -> Parser ParsedPath
parseDottedPath valueFinal = do
  firstToken <- consumeToken
  firstName <- case tokenKind firstToken of
    TokenIdentifier name | valueFinal -> pure name
    TokenConstructor name -> pure name
    _ -> parseFailureAt (tokenSpan firstToken) "path" "Expected a path"
  -- Module paths begin with a structure constructor.  A lowercase head is an
  -- ordinary value, so its following dots belong to record projection (for
  -- example @r.nm@), not to a qualified value path.
  more <- case tokenKind firstToken of
    TokenIdentifier _ -> pure []
    _ -> go
  let pieces = firstName : map fst more
      endAt = maybe (tokenSpan firstToken) (tokenSpan . snd) (lastMaybe more)
  when (not valueFinal && not (all startsUpper pieces)) (parseFailureAt endAt "constructor-path" "Expected a constructor path")
  pure (ParsedPath pieces (mergeSpans (tokenSpan firstToken) endAt))
  where
    go = do
      dot <- atText "."
      if not dot
        then pure []
        else do
          next <- peekKindN 1
          case next of
            Just (TokenConstructor name) -> do
              _ <- expectText "."
              token <- consumeToken
              ((name, token) :) <$> go
            Just (TokenIdentifier name) | valueFinal -> do
              _ <- expectText "."
              token <- consumeToken
              pure [(name, token)]
            _ -> pure []
    startsUpper [] = False
    startsUpper (character : _) = character >= 'A' && character <= 'Z'

pathToCon :: ParsedPath -> SConF
pathToCon path = case reverse (pathPieces path) of
  [] -> SCVar [] ""
  name : reversedModules -> SCVar (reverse reversedModules) name

valuePathExpression :: Inference -> Parser SExpr
valuePathExpression inference = do
  path <- parseValuePath
  case reverse (pathPieces path) of
    [] -> parseFailureAt (pathSpan path) "value-path" "Empty value path"
    name : reversedModules -> pure (Located (pathSpan path) (SEVar (reverse reversedModules) name inference))

expectNameConstant :: Parser (String, Span)
expectNameConstant = do
  token <- consumeToken
  case tokenKind token of
    TokenConstructor name -> pure (name, tokenSpan token)
    TokenInt value -> pure (show value, tokenSpan token)
    _ -> parseFailureAt (tokenSpan token) "name-constant" "Expected a constructor name or integer"

expectFieldName :: Parser (String, Token)
expectFieldName = do
  token <- consumeToken
  case tokenKind token of
    TokenConstructor name -> pure (name, token)
    TokenInt value -> pure (show value, token)
    _ -> parseFailureAt (tokenSpan token) "field-name" "Expected a field name"

parseWhileIdentifier :: Parser [String]
parseWhileIdentifier = do
  next <- peekKind
  case next of
    Just (TokenIdentifier name) -> consumeToken *> ((name :) <$> parseWhileIdentifier)
    _ -> pure []

parseCommaTail :: Parser value -> Parser [value]
parseCommaTail parser = do
  value <- parser
  more <- acceptText ","
  if more then (value :) <$> parseCommaTail parser else pure [value]

parseStarTail :: Parser value -> Parser [value]
parseStarTail parser = do
  value <- parser
  more <- acceptText "*"
  if more then (value :) <$> parseStarTail parser else pure [value]

parseSeparated :: String -> Parser value -> Parser [value]
parseSeparated separator parser = do
  more <- acceptText separator
  if more
    then do
      value <- parser
      (value :) <$> parseSeparated separator parser
    else pure []

tupleType :: Span -> [SCon] -> SCon
tupleType at constructors =
  let fields = zipWith (\index constructor -> (Located at (SCName (show index)), constructor)) [(1 :: Int) ..] constructors
   in Located at (SCTRecord (Located at (SCRecord fields)))

wildType :: Span -> SCon
wildType at = Located at (SCWild (Located at SKType))

entable :: SCon -> SCon
entable constructor = case locatedValue constructor of
  SCTRecord row -> row
  _ -> constructor

basisVar :: Span -> String -> SExpr
basisVar at name = Located at (SEVar ["Basis"] name Infer)

topVar :: Span -> String -> SExpr
topVar at name = Located at (SEVar ["Top"] name Infer)

basisUnary :: Span -> String -> SExpr -> SExpr
basisUnary at name argument = Located at (SEApp (basisVar at name) argument)

basisBinary :: Span -> String -> SExpr -> SExpr -> SExpr
basisBinary at name left right = Located at (SEApp (Located at (SEApp (basisVar at name) left)) right)

topBinary :: Span -> String -> SExpr -> SExpr -> SExpr
topBinary at name left right = Located at (SEApp (Located at (SEApp (topVar at name) left)) right)

basisPattern :: Span -> String -> SPattern
basisPattern at name = Located at (SPCon ["Basis"] name Nothing)

startsConTerm :: TokenKind -> Bool
startsConTerm token = case token of
  TokenIdentifier _ -> True
  TokenConstructor _ -> True
  TokenUnit -> True
  TokenKeyword "map" -> True
  TokenKeyword "fn" -> True
  TokenPunctuation punctuation' -> punctuation' `elem` ["(", "[", "{", "$", "#", "_"]
  _ -> False

startsExprTerm :: TokenKind -> Bool
startsExprTerm token = case token of
  TokenInt _ -> True
  TokenFloat _ -> True
  TokenString _ -> True
  TokenChar _ -> True
  TokenIdentifier _ -> True
  TokenConstructor _ -> True
  TokenUnit -> True
  TokenXmlBegin _ -> True
  TokenXmlBeginEnd _ -> True
  TokenPunctuation punctuation' -> punctuation' `elem` ["@", "_", "(", "{", "["]
  _ -> False

startsPatternTerm :: TokenKind -> Bool
startsPatternTerm token = case token of
  TokenIdentifier _ -> True
  TokenConstructor _ -> True
  TokenInt _ -> True
  TokenString _ -> True
  TokenChar _ -> True
  TokenUnit -> True
  TokenPunctuation punctuation' -> punctuation' `elem` ["_", "-", "(", "{", "["]
  _ -> False

disjointGuardAhead :: Parser Bool
disjointGuardAhead = gets inspect
  where
    inspect (Token _ (TokenPunctuation "[") : rest) = go 0 rest
    inspect _ = False
    go :: Int -> [Token] -> Bool
    go _ [] = False
    go depth (token : rest) = case tokenText token of
      Just "[" -> go (depth + 1) rest
      Just "]"
        | depth == 0 -> False
        | otherwise -> go (depth - 1) rest
      Just "~" | depth == 0 -> True
      _ -> go depth rest

tokenKindMaybe :: [Token] -> Maybe TokenKind
tokenKindMaybe [] = Nothing
tokenKindMaybe (token : _) = Just (tokenKind token)

tokenText :: Token -> Maybe String
tokenText token = case tokenKind token of
  TokenKeyword text -> Just text
  TokenPunctuation text -> Just text
  _ -> Nothing

peekToken :: Parser (Maybe Token)
peekToken = gets listHead

peekKind :: Parser (Maybe TokenKind)
peekKind = fmap tokenKind <$> peekToken

peekKindN :: Int -> Parser (Maybe TokenKind)
peekKindN index = gets (fmap tokenKind . atIndex index)

peekText :: Parser (Maybe String)
peekText = peekToken >>= pure . (>>= tokenText)

peekTextN :: Int -> Parser (Maybe String)
peekTextN index = gets ((>>= tokenText) . atIndex index)

atText :: String -> Parser Bool
atText expected = (== Just expected) <$> peekText

atAny :: [String] -> Parser Bool
atAny expected = maybe False (`elem` expected) <$> peekText

atEOF :: Parser Bool
atEOF = do
  next <- peekKind
  pure (next == Just TokenEOF || next == Nothing)

consumeToken :: Parser Token
consumeToken = do
  tokens <- get
  case tokens of
    [] -> parseFailureAt noSpan "unexpected-eof" "Unexpected end of input"
    token : rest -> put rest >> pure token

putBack :: Token -> Parser ()
putBack token = do
  tokens <- get
  put (token : tokens)

expectText :: String -> Parser Token
expectText expected = do
  token <- consumeToken
  if tokenText token == Just expected
    then pure token
    else parseFailureAt (tokenSpan token) "expected-token" ("Expected '" <> expected <> "'")

expectOneOf :: [String] -> Parser Token
expectOneOf expected = do
  token <- consumeToken
  if maybe False (`elem` expected) (tokenText token)
    then pure token
    else parseFailureAt (tokenSpan token) "expected-token" ("Expected one of " <> show expected)

acceptText :: String -> Parser Bool
acceptText expected = do
  matches <- atText expected
  when matches (consumeToken >> pure ())
  pure matches

expectIdentifier :: Parser (String, Token)
expectIdentifier = do
  token <- consumeToken
  case tokenKind token of
    TokenIdentifier name -> pure (name, token)
    _ -> parseFailureAt (tokenSpan token) "identifier" "Expected a lowercase identifier"

expectConstructor :: Parser (String, Token)
expectConstructor = do
  token <- consumeToken
  case tokenKind token of
    TokenConstructor name -> pure (name, token)
    _ -> parseFailureAt (tokenSpan token) "constructor-identifier" "Expected an uppercase identifier"

expectInteger :: Parser (Int64, Token)
expectInteger = do
  token <- consumeToken
  case tokenKind token of
    TokenInt value -> pure (value, token)
    _ -> parseFailureAt (tokenSpan token) "integer" "Expected an integer"

expectString :: Parser (BS.ByteString, Token)
expectString = do
  token <- consumeToken
  case tokenKind token of
    TokenString value -> pure (value, token)
    _ -> parseFailureAt (tokenSpan token) "string" "Expected a string"

expectXmlEnd :: Parser Token
expectXmlEnd = do
  token <- consumeToken
  case tokenKind token of
    TokenXmlEnd -> pure token
    _ -> parseFailureAt (tokenSpan token) "xml-end" "Expected closing XML root tag"

expectEOF :: Parser ()
expectEOF = do
  token <- consumeToken
  case tokenKind token of
    TokenEOF -> pure ()
    _ -> parseFailureAt (tokenSpan token) "trailing-input" "Unexpected trailing input"

parseFailure :: String -> String -> Parser value
parseFailure code message = do
  maybeToken <- peekToken
  parseFailureAt (maybe noSpan tokenSpan maybeToken) code message

parseFailureAt :: Span -> String -> String -> Parser value
parseFailureAt at code message = Parser (StateT (\_ -> Left (diagnostic ParsePhase code at message)))

ifM :: Monad monad => monad Bool -> monad value -> monad value -> monad value
ifM condition whenTrue whenFalse = do
  result <- condition
  if result then whenTrue else whenFalse

listHead :: [value] -> Maybe value
listHead [] = Nothing
listHead (value : _) = Just value

lastMaybe :: [value] -> Maybe value
lastMaybe [] = Nothing
lastMaybe values = Just (last values)

sndMaybe :: [(left, right)] -> Maybe right
sndMaybe = fmap snd . lastMaybe

atIndex :: Int -> [value] -> Maybe value
atIndex index values
  | index < 0 = Nothing
  | otherwise = go index values
  where
    go _ [] = Nothing
    go 0 (value : _) = Just value
    go remaining (_ : rest) = go (remaining - 1) rest
