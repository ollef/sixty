{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Compiler where

import qualified Data.ByteString.Lazy as Lazy
import Data.List (dropWhileEnd)
import Data.String (String)
import Low.Pretty as Pretty
import qualified Name
import qualified Paths_sixty as Paths
import Prettyprinter
import Prettyprinter.Util (putDocW)
import Protolude hiding (moduleName, wait, withAsync, (<.>))
import Query (Query)
import qualified Query
import Rock
import System.Directory
import System.FilePath
import System.Process

compile :: FilePath -> Bool -> FilePath -> Maybe String -> Bool -> Task Query ()
compile assemblyDir saveAssembly outputExecutableFile maybeOptimisationLevel printLowered = do
  let moduleAssemblyDir =
        assemblyDir </> "module"
  liftIO $ createDirectoryIfMissing True moduleAssemblyDir
  filePaths <- fetch Query.InputFiles

  moduleLLVMFiles <- forM (toList filePaths) \filePath -> do
    (moduleName@(Name.Module moduleNameText), _, _) <- fetch $ Query.ParsedFile filePath
    when printLowered do
      emptyPrettyEnv <- Pretty.emptyM moduleName
      liftIO $ putDocW 120 $ "module" <+> pretty moduleName <> line <> line
      defs <- fetch $ Query.LowModule moduleName
      forM_ defs \(defName, def) ->
        liftIO $ putDocW 120 $ Pretty.prettyDefinition emptyPrettyEnv defName def <> line <> line

    llvmModule <- fetch $ Query.LLVMModule moduleName
    let llvmFileName = moduleAssemblyDir </> toS moduleNameText <.> "ll"
    liftIO $ Lazy.writeFile llvmFileName llvmModule
    pure llvmFileName

  moduleInitLLVMFile <- do
    llvmModule <- fetch Query.LLVMModuleInitModule
    let llvmFileName = assemblyDir </> "module_init" <.> "ll"
    liftIO $ Lazy.writeFile llvmFileName llvmModule
    pure llvmFileName

  builtinLLVMFile <- liftIO $ Paths.getDataFileName "rts/Sixten.Builtin.ll"
  builtinCFile <- liftIO $ Paths.getDataFileName "rts/Sixten.Builtin.c"
  mainLLVMFile <- liftIO $ Paths.getDataFileName "rts/main.ll"
  garbageCollectorCFile <- liftIO $ Paths.getDataFileName "rts/garbage_collector.c"
  let llvmFiles =
        mainLLVMFile : builtinLLVMFile : moduleInitLLVMFile : moduleLLVMFiles
  let optimisationArgs =
        maybe [] (\o -> ["-O" <> o]) maybeOptimisationLevel
  clang <- liftIO clangBinPath
  liftIO
    if saveAssembly
      then do
        let linkedProgramName =
              assemblyDir </> "program" <.> "ll"
            optimisedProgramName =
              assemblyDir </> "program-opt" <.> "ll"
            builtinCLLFile =
              assemblyDir </> "Sixten.Builtin" <.> "c" <.> "ll"
            garbageCollectorLLFile =
              assemblyDir </> "garbage_collector" <.> "ll"
        llvmBin <- liftIO llvmBinPath
        callProcess clang $ optimisationArgs <> ["-fPIC", "-Wno-override-module", "-S", "-emit-llvm", "-o", builtinCLLFile, builtinCFile]
        callProcess clang $ optimisationArgs <> ["-fPIC", "-Wno-override-module", "-S", "-emit-llvm", "-o", garbageCollectorLLFile, garbageCollectorCFile]
        callProcess (llvmBin </> "llvm-link") $ ["-S", "-o", linkedProgramName, builtinCLLFile, garbageCollectorLLFile] <> llvmFiles
        callProcess (llvmBin </> "opt") $ optimisationArgs <> ["-S", "-o", optimisedProgramName, linkedProgramName]
        callProcess clang $ optimisationArgs <> ["-fPIC", "-Wno-override-module", "-o", outputExecutableFile, linkedProgramName]
      else callProcess clang $ optimisationArgs <> ["-fPIC", "-Wno-override-module", "-o", outputExecutableFile, builtinCFile, garbageCollectorCFile] <> llvmFiles

supportedLlvmVersions :: [Int]
supportedLlvmVersions = [17, 16, 15]

-- | llvm-config is not available in current LLVM distribution for windows, so we
-- need use @clang -print-prog-name=clang@ to get the full path of @clang@.
--
-- We simply assume that @clang.exe@ already exists in @%PATH%@.
--
-- TODO configurable clang path
clangBinPath :: IO FilePath
clangBinPath = trim <$> checkClangExists
  where
    checkClangExists =
      handle (\(_ :: IOException) -> panic "Couldn't find clang.") $
        readProcess "clang" ["-print-prog-name=clang"] ""
    trim = dropWhile isSpace . dropWhileEnd isSpace

-- TODO configurable llvm bin path
llvmBinPath :: IO FilePath
llvmBinPath = trim <$> checkLlvmExists candidates
  where
    suffixes =
      ""
        -- The naming scheme on e.g. Ubuntu:
        : fmap (('-' :) . show) supportedLlvmVersions
    prefixes =
      [ ""
      , -- The installation path of Brew on Mac:
        "/usr/local/opt/llvm/bin/"
      ]
    candidates =
      ["llvm-config" <> suffix | suffix <- suffixes]
        ++ [prefix <> "llvm-config" | prefix <- prefixes]

    checkLlvmExists :: [String] -> IO FilePath
    checkLlvmExists (path : xs) =
      handle (\(_ :: IOException) -> checkLlvmExists xs) $
        readProcess path ["--bindir"] ""
    checkLlvmExists [] =
      panic "Couldn't find llvm-config."

    trim = dropWhile isSpace . dropWhileEnd isSpace
