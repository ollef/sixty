{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TupleSections #-}
{-# language TypeFamilies #-}
module Driver where

import Protolude hiding (force, State, state)

import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import qualified Data.HashSet as HashSet
import qualified Data.Text.IO as Text
import Rock

import Error (Error)
import qualified Error.Hydrated as Error (Hydrated)
import qualified Error.Hydrated
import qualified Name
import Query (Query)
import qualified Query
import qualified Rules
import qualified Syntax

runTask :: [FilePath] -> (Error.Hydrated -> Task Query err) -> Task Query a -> IO (a, [err])
runTask files prettyError task = do
  startedVar <- newMVar mempty
  errorsVar <- newMVar (mempty :: DMap Query (Const [Error]))
  let
    writeErrors :: Writer TaskKind Query a -> [Error] -> Task Query ()
    writeErrors (Writer q) errs =
      unless (null errs) $
        liftIO $ modifyMVar_ errorsVar $ pure . DMap.insert q (Const errs)

    ignoreTaskKind :: Query a -> TaskKind -> Task Query ()
    ignoreTaskKind _ _ =
      pure ()

    rules :: Rules Query
    rules =
      -- traceFetch (\q -> liftIO $ putText $ "fetching " <> show q) (\q _ -> liftIO $ putText $ "fetched " <> show q) $
      memoise startedVar $
      writer ignoreTaskKind $
      writer writeErrors $
      Rules.rules files readFile

  Rock.runTask sequentially rules $ do
    result <- task
    errorsMap <- liftIO $ readMVar errorsVar
    let
      errors =
        flip foldMap (DMap.toList errorsMap) $ \(_ DMap.:=> Const errs) ->
          errs
    prettyErrors <- forM errors (prettyError <=< Error.Hydrated.fromError)
    pure (result, prettyErrors)

-------------------------------------------------------------------------------
-- Incremental execution
data State err = State
  { _tracesVar :: !(MVar (Traces Query))
  , _errorsVar :: !(MVar (DMap Query (Const [err])))
  }

initialState :: IO (State err)
initialState = do
  tracesVar <- newMVar mempty
  errorsVar <- newMVar mempty
  return State
    { _tracesVar = tracesVar
    , _errorsVar = errorsVar
    }

data Prune
  = Don'tPrune
  | Prune

runIncrementalTask
  :: State err
  -> FilePath
  -> Text
  -> (Error.Hydrated -> Task Query err)
  -> Prune
  -> Task Query a
  -> IO (a, [err])
runIncrementalTask state file text prettyError prune task =
  handleEx $ do
    startedVar <- newMVar mempty
    -- printVar <- newMVar 0
    let
      readSourceFile_ file'
        | file == file' = return text
        | otherwise = readFile file'
      traceFetch_
        :: GenRules (Writer TaskKind Query) Query
        -> GenRules (Writer TaskKind Query) Query
      traceFetch_ = identity
        -- traceFetch
        --   (\(Writer key) -> liftIO $ modifyMVar_ printVar $ \n -> do
        --     _logAction logEnv_ $ fold (replicate n "| ") <> "fetching " <> show key
        --     return $ n + 1)
        --   (\_ _ -> liftIO $ modifyMVar_ printVar $ \n -> do
        --     _logAction logEnv_ $ fold (replicate (n - 1) "| ") <> "*"
        --     return $ n - 1)
      writeErrors :: Writer TaskKind Query a -> [Error] -> Task Query ()
      writeErrors (Writer key) errs = do
        errs' <- mapM (prettyError <=< Error.Hydrated.fromError) errs
        liftIO $
          modifyMVar_ (_errorsVar state) $
            pure . DMap.insert key (Const errs')
      tasks :: Rules Query
      tasks =
        memoise startedVar $
        verifyTraces (_tracesVar state) $
        traceFetch_ $
        writer writeErrors $
        Rules.rules (pure file) readSourceFile_
    result <- Rock.runTask sequentially tasks task
    started <- readMVar startedVar
    errorsMap <- case prune of
      Don'tPrune ->
        readMVar $ _errorsVar state

      Prune -> do
        modifyMVar_ (_tracesVar state) $
          pure . DMap.intersectionWithKey (\_ _ t -> t) started
        modifyMVar (_errorsVar state) $ \errors -> do
          let
            errors' = DMap.intersectionWithKey (\_ _ e -> e) started errors
          return (errors', errors')
    let
      errors = do
        (_ DMap.:=> Const errs) <- DMap.toList errorsMap
        errs
    return (result, errors)
  where
    handleEx m = do
      mres <- try m
      case mres of
        Left e -> do
          Text.hPutStrLn stderr $ "exception! " <> show (e :: SomeException)
          panic "a"

        Right res ->
          return res

-------------------------------------------------------------------------------

checkAll :: [FilePath] -> Task Query [(FilePath, [(Name.Qualified, Maybe Syntax.Definition, Syntax.Type Void)])]
checkAll filePaths = do
  forM filePaths $ \filePath -> (filePath, ) <$> do
    (module_, _, defs) <- fetch $ Query.ParsedFile filePath
    let
      names =
        HashSet.fromList $
          Name.Qualified module_ . fst . snd <$> defs
    forM (HashSet.toList names) $ \name -> do
      type_ <- fetch $ Query.ElaboratedType name
      maybeDef <- fetch $ Query.ElaboratedDefinition name
      pure (name, fst <$> maybeDef, type_)
