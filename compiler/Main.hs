module Main (main) where

import Browser (emitBrowser)
import Control.Exception (SomeException, displayException, try)
import qualified Data.ByteString as BS
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Vr (compileProjectToMono, monomorphicProjectFile, renderDiagnostic)

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    [library, project, capabilities, output] -> do
      result <- try $ do
        supported <- Set.fromList . words . Text.unpack . Text.decodeUtf8 <$> BS.readFile capabilities
        mono <- compileProjectToMono library project
        case mono >>= emitBrowser supported . monomorphicProjectFile of
          Left problems -> do
            mapM_ (hPutStrLn stderr . renderDiagnostic) problems
            pure False
          Right javascript -> BS.writeFile output (Text.encodeUtf8 (Text.pack javascript)) >> pure True
      case result of
        Right True -> pure ()
        Right False -> exitFailure
        Left exception -> hPutStrLn stderr ("Compiler failed: " <> displayException (exception :: SomeException)) >> exitFailure
    _ -> hPutStrLn stderr "usage: vr-browser LIBRARY PROJECT CAPABILITIES OUTPUT" >> exitFailure
