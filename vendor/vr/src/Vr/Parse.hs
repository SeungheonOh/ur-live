-- | Public parsing facade.  Lexer state, parser mechanics, syntax families,
-- SQL, and XML live in focused internal modules under @Vr.Parse@.
module Vr.Parse
  ( Token (..)
  , TokenKind (..)
  , lexSource
  , parseImplementation
  , parseSignature
  ) where

import qualified Data.ByteString as BS
import Vr.Parse.Core (expectEOF, runParser)
import Vr.Parse.Declaration (parseDeclarationsUntil, parseSignatureItemsUntil)
import Vr.Parse.Lexer
import Vr.Source

parseImplementation :: FilePath -> BS.ByteString -> Either [Diagnostic] SFile
parseImplementation file bytes =
  let (tokens, problems) = lexSource file bytes
   in if null problems
        then case runParser (parseDeclarationsUntil [] <* expectEOF) tokens of
          Left problem -> Left [problem]
          Right declarations -> Right declarations
        else Left problems

parseSignature :: FilePath -> BS.ByteString -> Either [Diagnostic] [SSigItem]
parseSignature file bytes =
  let (tokens, problems) = lexSource file bytes
   in if null problems
        then case runParser (parseSignatureItemsUntil [] <* expectEOF) tokens of
          Left problem -> Left [problem]
          Right items -> Right items
        else Left problems
