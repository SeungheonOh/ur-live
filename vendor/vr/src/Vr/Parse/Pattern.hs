module Vr.Parse.Pattern
  ( parsePattern
  , parsePatternTerm
  ) where

import Control.Monad.State.Strict (gets)
import Vr.Parse.Core
import Vr.Parse.Lexer
import Vr.Parse.Type
import Vr.Source
parsePattern :: Parser SPattern
parsePattern = do
  first <- parsePatternTerm
  annotation <- acceptText ":"
  if annotation
    then do
      valueType <- parseCon
      pure (Located (mergeSpans (locatedSpan first) (locatedSpan valueType)) (SPAnnot first valueType))
    else do
      cons <- acceptText "::"
      if cons
        then do
          rest <- parsePattern
          let at = mergeSpans (locatedSpan first) (locatedSpan rest)
              payload = Located at (SPRecord [("1", first), ("2", rest)] False)
          pure (Located at (SPCon ["Basis"] "Cons" (Just payload)))
        else pure first

parsePatternTerm :: Parser SPattern
parsePatternTerm = do
  next <- peekKind
  case next of
    Just (TokenIdentifier name) -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SPVar name))
    Just (TokenConstructor _) -> do
      path <- parseConstructorPath
      argumentAhead <- gets (maybe False startsPatternTerm . tokenKindMaybe)
      argument <- if argumentAhead then Just <$> parsePatternTerm else pure Nothing
      let at = maybe (pathSpan path) (mergeSpans (pathSpan path) . locatedSpan) argument
          pieces = pathPieces path
      case reverse pieces of
        [] -> parseFailureAt at "pattern-constructor" "Empty constructor path"
        name : modulesReversed -> pure (Located at (SPCon (reverse modulesReversed) name argument))
    Just (TokenPunctuation "_") -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SPVar "_"))
    Just (TokenInt value) -> primitivePattern (PrimInt value)
    Just (TokenString value) -> primitivePattern (PrimString NormalString value)
    Just (TokenChar value) -> primitivePattern (PrimChar value)
    Just (TokenPunctuation "-") -> do
      start <- consumeToken
      (value, end) <- expectInteger
      pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SPPrim (PrimInt (negate value))))
    Just TokenUnit -> do
      token <- consumeToken
      pure (Located (tokenSpan token) (SPRecord [] False))
    Just (TokenPunctuation "(") -> parseParenthesizedPattern
    Just (TokenPunctuation "{") -> parseRecordPattern
    Just (TokenPunctuation "[") -> do
      start <- consumeToken
      end <- expectText "]"
      pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SPCon ["Basis"] "Nil" Nothing))
    _ -> parseFailure "pattern" "Expected a pattern"
  where
    primitivePattern primitive = do
      token <- consumeToken
      pure (Located (tokenSpan token) (SPPrim primitive))

parseParenthesizedPattern :: Parser SPattern
parseParenthesizedPattern = do
  start <- expectText "("
  first <- parsePattern
  tuple <- acceptText ","
  if tuple
    then do
      rest <- parseCommaTail parsePattern
      end <- expectText ")"
      let at = mergeSpans (tokenSpan start) (tokenSpan end)
          fields = zipWith (\index pattern' -> (show index, pattern')) [(1 :: Int) ..] (first : rest)
      pure (Located at (SPRecord fields False))
    else do
      _ <- expectText ")"
      pure first

parseRecordPattern :: Parser SPattern
parseRecordPattern = do
  start <- expectText "{"
  empty <- acceptText "}"
  if empty
    then pure (Located (tokenSpan start) (SPRecord [] False))
    else do
      flexible <- acceptText "..."
      if flexible
        then do
          end <- expectText "}"
          pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SPRecord [] True))
        else do
          (name, _) <- expectFieldName
          _ <- expectText "="
          pattern' <- parsePattern
          (rest, isFlexible) <- parseMorePatternFields
          end <- expectText "}"
          pure (Located (mergeSpans (tokenSpan start) (tokenSpan end)) (SPRecord ((name, pattern') : rest) isFlexible))

parseMorePatternFields :: Parser ([(String, SPattern)], Bool)
parseMorePatternFields = do
  comma <- acceptText ","
  if not comma
    then pure ([], False)
    else do
      flexible <- acceptText "..."
      if flexible
        then pure ([], True)
        else do
          (name, _) <- expectFieldName
          _ <- expectText "="
          pattern' <- parsePattern
          (rest, isFlexible) <- parseMorePatternFields
          pure ((name, pattern') : rest, isFlexible)

