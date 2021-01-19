{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Compiler where

import qualified Builtin
import qualified Data.Text.Lazy.IO as Lazy
import Data.Text.Prettyprint.Doc
import LLVM.Pretty (ppllvm)
import qualified Paths_sixty as Paths
import Protolude hiding (withAsync, wait, moduleName, (<.>))
import Query (Query)
import qualified Query
import Rock
import System.FilePath
import System.Process
import System.Directory

compile :: [FilePath] -> FilePath -> FilePath -> Task Query ()
compile filePaths assemblyDir outputExecutableFile = do
  builtinFile <- fromMaybe "Compiler: panic no builtin file" <$> fetch (Query.ModuleFile Builtin.Module)
  let
    moduleAssemblyDir =
      assemblyDir </> "module"
  liftIO $ createDirectoryIfMissing True moduleAssemblyDir
  moduleLLVMFiles <- forM (builtinFile : filePaths) $ \filePath -> do
    (moduleName, _, _) <- fetch $ Query.ParsedFile filePath
    llvmModule <- fetch $ Query.LLVMModule moduleName
    let
      llvmFileName =
        moduleAssemblyDir </> takeBaseName filePath <.> "ll"
    liftIO $ Lazy.writeFile llvmFileName $ ppllvm llvmModule
    pure llvmFileName

  builtinLLVMFile <- liftIO $ Paths.getDataFileName "rts/Sixten.Builtin.ll"
  initCFile <- liftIO $ Paths.getDataFileName "rts/init.c"
  let
    llvmFiles =
      builtinLLVMFile : moduleLLVMFiles
  -- TODO configurable clang path
  liftIO $ callProcess "clang" $ ["-fPIC", "-o", outputExecutableFile, initCFile] <> llvmFiles
