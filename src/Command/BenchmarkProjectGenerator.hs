{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RecordWildCards #-}
module Command.BenchmarkProjectGenerator where

import Protolude hiding ((<.>), moduleName, functionName)

import System.Directory
import System.FilePath
import System.Random
import qualified Data.Text as Text
import Data.List ((!!))

data Options = Options
  { outputDirectory :: FilePath
  , moduleCount :: !Int
  , importCount :: !Int
  , functionCount :: !Int
  }

generate :: Options -> IO ()
generate Options {..} = do
  createDirectoryIfMissing True $ outputDirectory </> "src"
  forM_ [1..moduleCount] $ \moduleNumber -> do
    let
      moduleName num =
        "Module" <> show num

      functionName num =
        "f" <> show num

    importedModules <- replicateM (min (moduleNumber - 1) importCount) $
      randomRIO (1, moduleNumber - 1)

    functions <- forM [1..functionCount] $ \functionNumber -> do
      def <-
        if not (null importedModules) then do
          module1 <- (importedModules !!) <$> randomRIO (0, length importedModules - 1)
          module2 <- (importedModules !!) <$> randomRIO (0, length importedModules - 1)
          function1 <- randomRIO (1, functionCount)
          function2 <- randomRIO (1, functionCount)
          pure
            $ moduleName module1 <> "." <> functionName function1 <> " -> "
            <> moduleName module2 <> "." <> functionName function2
        else
          pure "Type"
      pure (functionNumber, def)

    writeFile (outputDirectory </> "src" </> moduleName moduleNumber <.> "vix") $
      Text.unlines
      [ "module " <> moduleName moduleNumber <> " exposing (..)"
      , ""
      , Text.unlines
        [ "import " <> moduleName importedModule
        | importedModule <- importedModules
        ]
      , Text.unlines
        [ Text.unlines
          [ functionName functionNumber <> " : Type"
          , functionName functionNumber <> " = " <> def
          ]
        | (functionNumber, def) <- functions
        ]
      ]

  writeFile (outputDirectory </> "sixten.json") "{ \"source-directories\": [ \"src\" ] }"
