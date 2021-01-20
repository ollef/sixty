module Command.Run where

import Command.Compile (withCompiledExecutable)
import Data.String (String)
import Protolude
import System.Process

run :: [FilePath] -> Maybe FilePath -> Maybe FilePath -> Maybe String -> IO ()
run =
  withCompiledExecutable $ \exe -> callProcess exe []
