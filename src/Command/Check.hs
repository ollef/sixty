{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Command.Check where

import Control.Concurrent.Async.Lifted.Safe
import qualified Core.Pretty as Pretty
import qualified Core.Syntax as Syntax
import qualified Data.HashSet as HashSet
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text (putDoc)
import Data.Time.Clock
import qualified Driver
import qualified Error.Hydrated
import qualified Name
import qualified Project
import Protolude hiding (wait, withAsync)
import qualified Query
import Rock

check :: [FilePath] -> Bool -> IO ()
check argumentFiles printElaborated = do
  startTime <- getCurrentTime
  (sourceDirectories, filePaths) <- Project.filesFromArguments argumentFiles
  ((), errs) <-
    Driver.runTask sourceDirectories filePaths Error.Hydrated.pretty $
      if printElaborated
        then withAsync (void Driver.checkAll) $ \checkedAll -> do
          inputFiles <- fetch Query.InputFiles
          forM_ inputFiles $ \filePath -> do
            (module_, _, defs) <- fetch $ Query.ParsedFile filePath
            let names =
                  HashSet.fromList $
                    Name.Qualified module_ . fst . snd <$> defs
            emptyPrettyEnv <- Pretty.emptyM module_
            liftIO $ putDoc $ "module" <+> pretty module_ <> line <> line
            forM_ names $ \name -> do
              type_ <- fetch $ Query.ElaboratedType name
              liftIO $ putDoc $ Pretty.prettyDefinition emptyPrettyEnv name (Syntax.TypeDeclaration type_) <> line
              maybeDef <- fetch $ Query.ElaboratedDefinition name
              liftIO $ do
                forM_ maybeDef $ \(def, _) ->
                  putDoc $ Pretty.prettyDefinition emptyPrettyEnv name def <> line
                putDoc line
          wait checkedAll
        else void Driver.checkAll
  endTime <- getCurrentTime
  forM_ errs $ \err ->
    putDoc $ err <> line
  let errorCount =
        length errs
  putText $
    Text.unwords
      [ "Found"
      , show errorCount
      , case errorCount of
          1 -> "error"
          _ -> "errors"
      , "in"
      , show (diffUTCTime endTime startTime) <> "."
      ]
  unless
    (null errs)
    exitFailure
