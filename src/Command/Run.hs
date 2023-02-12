{-# LANGUAGE BlockArguments #-}

module Command.Run where

import qualified Command.Compile
import Protolude
import System.Process

run :: Command.Compile.Options -> IO ()
run =
  Command.Compile.withCompiledExecutable \exe -> callProcess exe []
