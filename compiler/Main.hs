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
    [library, project, capabilities, output] -> compile library project capabilities output Nothing
    [library, project, capabilities, output, entryModule] -> compile library project capabilities output (Just entryModule)
    _ -> hPutStrLn stderr "usage: vr-browser LIBRARY PROJECT CAPABILITIES OUTPUT [ENTRY_MODULE]" >> exitFailure

compile :: FilePath -> FilePath -> FilePath -> FilePath -> Maybe String -> IO ()
compile library project capabilities output entryModule = do
  result <- try $ do
    supported <- Set.fromList . words . Text.unpack . Text.decodeUtf8 <$> BS.readFile capabilities
    mono <- compileProjectToMono library project
    case mono >>= emitBrowser supported entryModule . monomorphicProjectFile of
      Left problems -> do
        mapM_ (hPutStrLn stderr . renderDiagnostic) problems
        pure False
      Right javascript -> BS.writeFile output (Text.encodeUtf8 (Text.pack javascript)) >> pure True
  case result of
    Right True -> pure ()
    Right False -> exitFailure
    Left exception -> hPutStrLn stderr ("Compiler failed: " <> displayException (exception :: SomeException)) >> exitFailure
