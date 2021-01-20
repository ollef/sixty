{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Compiler where

import qualified Data.Text.Lazy.IO as Lazy
import Data.Text.Prettyprint.Doc
import LLVM.Pretty (ppllvm)
import qualified Name
import qualified Paths_sixty as Paths
import Protolude hiding (withAsync, wait, moduleName, (<.>))
import Query (Query)
import qualified Query
import Rock
import System.Directory
import System.FilePath
import System.Process

compile :: FilePath -> FilePath -> Task Query ()
compile assemblyDir outputExecutableFile = do
  let
    moduleAssemblyDir =
      assemblyDir </> "module"
  liftIO $ createDirectoryIfMissing True moduleAssemblyDir
  filePaths <- fetch Query.InputFiles
  moduleLLVMFiles <- forM (toList filePaths) $ \filePath -> do
    (moduleName@(Name.Module moduleNameText), _, _) <- fetch $ Query.ParsedFile filePath
    llvmModule <- fetch $ Query.LLVMModule moduleName
    let
      llvmFileName =
        moduleAssemblyDir </> toS moduleNameText <.> "ll"
    liftIO $ Lazy.writeFile llvmFileName $ ppllvm llvmModule
    pure llvmFileName

  moduleInitLLVMFile <- do
    llvmModule <- fetch Query.LLVMModuleInitModule
    let
      llvmFileName =
        assemblyDir </> "module_init" <.> "ll"
    liftIO $ Lazy.writeFile llvmFileName $ ppllvm llvmModule
    pure llvmFileName

  builtinLLVMFile <- liftIO $ Paths.getDataFileName "rts/Sixten.Builtin.ll"
  mainLLVMFile <- liftIO $ Paths.getDataFileName "rts/main.ll"
  initCFile <- liftIO $ Paths.getDataFileName "rts/init.c"
  let
    llvmFiles =
      mainLLVMFile : builtinLLVMFile : moduleInitLLVMFile : moduleLLVMFiles
  -- TODO configurable clang path
  liftIO $ callProcess "clang" $ ["-fPIC", "-Wno-override-module", "-o", outputExecutableFile, initCFile] <> llvmFiles
