-- Only used by the native facade's bundled-path convenience functions. The
-- playground entry point explicitly supplies its virtual standard-library root.
module Paths_vr (getDataFileName) where

getDataFileName :: FilePath -> IO FilePath
getDataFileName path = pure ("/vr/" <> path)
