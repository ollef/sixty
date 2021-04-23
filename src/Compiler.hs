{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Compiler where

import Data.String (String)
import qualified Data.Text.Lazy.IO as Lazy
import Data.Text.Prettyprint.Doc
import LLVM.Pretty (ppllvm)
import qualified Name
import qualified Paths_sixty as Paths
import Protolude hiding (moduleName, wait, withAsync, (<.>))
import Query (Query)
import qualified Query
import Rock
import System.Directory
import System.FilePath
import System.Process

compile :: FilePath -> Bool -> FilePath -> Maybe String -> Task Query ()
compile assemblyDir saveAssembly outputExecutableFile maybeOptimisationLevel = do
  let moduleAssemblyDir =
        assemblyDir </> "module"
  liftIO $ createDirectoryIfMissing True moduleAssemblyDir
  filePaths <- fetch Query.InputFiles
  moduleLLVMFiles <- forM (toList filePaths) $ \filePath -> do
    (moduleName@(Name.Module moduleNameText), _, _) <- fetch $ Query.ParsedFile filePath
    llvmModule <- fetch $ Query.LLVMModule moduleName
    let llvmFileName =
          moduleAssemblyDir </> toS moduleNameText <.> "ll"
    liftIO $ Lazy.writeFile llvmFileName $ ppllvm llvmModule
    pure llvmFileName

  moduleInitLLVMFile <- do
    llvmModule <- fetch Query.LLVMModuleInitModule
    let llvmFileName =
          assemblyDir </> "module_init" <.> "ll"
    liftIO $ Lazy.writeFile llvmFileName $ ppllvm llvmModule
    pure llvmFileName

  builtinLLVMFile <- liftIO $ Paths.getDataFileName "rts/Sixten.Builtin.ll"
  builtinCFile <- liftIO $ Paths.getDataFileName "rts/Sixten.Builtin.c"
  mainLLVMFile <- liftIO $ Paths.getDataFileName "rts/main.ll"
  globalsCFile <- liftIO $ Paths.getDataFileName "rts/globals.c"
  let llvmFiles =
        mainLLVMFile : builtinLLVMFile : moduleInitLLVMFile : moduleLLVMFiles
  -- TODO configurable clang path
  let optimisationArgs =
        maybe [] (\o -> ["-O" <> o]) maybeOptimisationLevel
  liftIO $
    if saveAssembly
      then do
        let linkedProgramName =
              assemblyDir </> "program" <.> "ll"
            optimisedProgramName =
              assemblyDir </> "program-opt" <.> "ll"
            builtinCLLFile =
              assemblyDir </> "Sixten.Builtin" <.> "c" <.> "ll"
            globalsLLFile =
              assemblyDir </> "globals" <.> "ll"
        callProcess "clang" $ optimisationArgs <> ["-fPIC", "-Wno-override-module", "-S", "-emit-llvm", "-o", builtinCLLFile, builtinCFile]
        callProcess "clang" $ optimisationArgs <> ["-fPIC", "-Wno-override-module", "-S", "-emit-llvm", "-o", globalsLLFile, globalsCFile]
        callProcess "llvm-link" $ ["-S", "-o", linkedProgramName, builtinCLLFile, globalsLLFile] <> llvmFiles
        callProcess "opt" $ optimisationArgs <> ["-S", "-o", optimisedProgramName, linkedProgramName]
        callProcess "clang" $ optimisationArgs <> ["-fPIC", "-Wno-override-module", "-o", outputExecutableFile, linkedProgramName]
      else callProcess "clang" $ optimisationArgs <> ["-fPIC", "-Wno-override-module", "-o", outputExecutableFile, builtinCFile, globalsCFile] <> llvmFiles
