{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language TupleSections #-}
{-# language TypeFamilies #-}
module Driver where

import Protolude hiding (force, State, state)

import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.HashSet (HashSet)
import Data.IORef
import Data.Persist (Persist)
import qualified Data.Persist as Persist
import qualified Data.Text.IO as Text
import Rock

import Error (Error)
import qualified Error.Hydrated as Error (Hydrated)
import qualified Error.Hydrated
import HashTag
import qualified Name
import qualified Paths_sixty as Paths
import Query (Query)
import qualified Query
import qualified Rules

runTask
  :: [FilePath]
  -> HashSet FilePath
  -> (Error.Hydrated -> Task Query err)
  -> Task Query a
  -> IO (a, [err])
runTask sourceDirectories files prettyError task = do
  startedVar <- newIORef mempty
  errorsVar <- newIORef (mempty :: DMap Query (Const [Error]))
  -- printVar <- newMVar 0
  let
    writeErrors :: Writer TaskKind Query a -> [Error] -> Task Query ()
    writeErrors (Writer q) errs =
      unless (null errs) $
        liftIO $ atomicModifyIORef errorsVar $ (, ()) . DMap.insert q (Const errs)

    ignoreTaskKind :: Query a -> TaskKind -> Task Query ()
    ignoreTaskKind _ _ =
      pure ()

--     traceFetch_
--       :: GenRules (Writer TaskKind Query) Query
--       -> GenRules (Writer TaskKind Query) Query
--     traceFetch_ =
--       traceFetch
--         (\(Writer key) -> liftIO $ modifyMVar_ printVar $ \n -> do
--           putText $ fold (replicate n "| ") <> "fetching " <> show key
--           return $ n + 1)
--         (\_ _ -> liftIO $ modifyMVar_ printVar $ \n -> do
--           putText $ fold (replicate (n - 1) "| ") <> "*"
--           return $ n - 1)

    rules :: Rules Query
    rules =
      memoise startedVar $
      writer ignoreTaskKind $
      -- traceFetch_ $
      writer writeErrors $
      Rules.rules sourceDirectories files $ \file ->
        readFile file `catch` \(_ :: IOException) -> pure mempty

  Rock.runTask sequentially rules $ do
  -- Rock.runMemoisedTask startedVar rules $ do
    result <- task
    errorsMap <- liftIO $ readIORef errorsVar
    let
      errors =
        flip foldMap (DMap.toList errorsMap) $ \(_ DMap.:=> Const errs) ->
          errs
    prettyErrors <- forM errors (prettyError <=< Error.Hydrated.fromError)
    pure (result, prettyErrors)

-------------------------------------------------------------------------------
-- Incremental execution
data State err = State
  { _startedVar :: !(IORef (DMap Query MVar))
  , _hashesVar :: !(IORef (DMap Query (Const Int)))
  , _reverseDependenciesVar :: !(IORef (ReverseDependencies Query))
  , _tracesVar :: !(IORef (Traces Query (Const Int)))
  , _errorsVar :: !(IORef (DMap Query (Const [err])))
  }

initialState :: IO (State err)
initialState = do
  startedVar <- newIORef mempty
  hashesVar <- newIORef mempty
  reverseDependenciesVar <- newIORef mempty
  tracesVar <- newIORef mempty
  errorsVar <- newIORef mempty
  return State
    { _startedVar = startedVar
    , _hashesVar = hashesVar
    , _reverseDependenciesVar = reverseDependenciesVar
    , _tracesVar = tracesVar
    , _errorsVar = errorsVar
    }

encodeState :: Persist err => State (err, doc) -> IO ByteString
encodeState state = do
  traces <- readIORef $ _tracesVar state
  errors <- readIORef $ _errorsVar state
  pure $
    Persist.encode (traces, DMap.map (\(Const errDocs) -> Const $ fst <$> errDocs) errors)

decodeState :: Persist err => ByteString -> IO (State err)
decodeState bs = do
  s <- initialState
  case Persist.decode bs of
    Right (traces, errors) -> do
      void $ atomicWriteIORef (_tracesVar s) traces
      void $ atomicWriteIORef (_errorsVar s) errors
    Left _ ->
      pure ()
  pure s

data Prune
  = Don'tPrune
  | Prune

runIncrementalTask
  :: State err
  -> HashSet FilePath
  -> [FilePath]
  -> HashMap FilePath Text
  -> (Error.Hydrated -> Task Query err)
  -> Prune
  -> Task Query a
  -> IO (a, [err])
runIncrementalTask state changedFiles sourceDirectories files prettyError prune task =
  handleEx $ do
    do
      reverseDependencies <- readIORef $ _reverseDependenciesVar state
      started <- readIORef $ _startedVar state
      hashes <- readIORef $ _hashesVar state

      case DMap.lookup Query.InputFiles started of
        Nothing -> do
          atomicWriteIORef (_reverseDependenciesVar state) mempty
          atomicWriteIORef (_startedVar state) mempty
          atomicWriteIORef (_hashesVar state) mempty

        Just inputFilesVar -> do
          inputFiles <- readMVar inputFilesVar
          -- TODO find a nicer way to do this
          builtinFile <- Paths.getDataFileName "builtin/Builtin.vix"
          if inputFiles /= HashSet.insert builtinFile (HashSet.fromMap $ void files) then do
            atomicWriteIORef (_reverseDependenciesVar state) mempty
            atomicWriteIORef (_startedVar state) mempty
            atomicWriteIORef (_hashesVar state) mempty

          else do
            changedFiles' <- flip filterM (toList changedFiles) $ \file ->
              case DMap.lookup (Query.FileText file) started of
                Just resultVar -> do
                  text <- readMVar resultVar
                  pure $ Just text /= HashMap.lookup file files

                Nothing ->
                  pure True
            -- Text.hPutStrLn stderr $ "Driver changed files " <> show changedFiles'
            let
              (keysToInvalidate, reverseDependencies') =
                foldl'
                  (\(keysToInvalidate_, reverseDependencies_) file ->
                    first (<> keysToInvalidate_) $ reachableReverseDependencies (Query.FileText file) reverseDependencies_
                  )
                  (mempty, reverseDependencies)
                  changedFiles'
            let
              started' =
                DMap.difference started keysToInvalidate

              hashes' =
                DMap.difference hashes keysToInvalidate
            -- Text.hPutStrLn stderr $ "keysToInvalidate " <> show (DMap.size keysToInvalidate)
            -- Text.hPutStrLn stderr $ "Started " <> show (DMap.size started) <> " -> " <> show (DMap.size started')
            -- Text.hPutStrLn stderr $ "Hashes " <> show (DMap.size hashes) <> " -> " <> show (DMap.size hashes')
            -- Text.hPutStrLn stderr $ "ReverseDependencies " <> show (Map.size reverseDependencies) <> " -> " <> show (Map.size reverseDependencies')

            atomicWriteIORef (_startedVar state) started'
            atomicWriteIORef (_hashesVar state) hashes'
            atomicWriteIORef (_reverseDependenciesVar state) reverseDependencies'

    -- printVar <- newMVar 0
    let
      readSourceFile_ file
        | Just text <- HashMap.lookup file files =
          return text
        | otherwise =
          readFile file `catch` \(_ :: IOException) -> pure mempty

      traceFetch_
        :: GenRules (Writer TaskKind Query) Query
        -> GenRules (Writer TaskKind Query) Query
      traceFetch_ = identity
      -- traceFetch_ =
      --   traceFetch
      --     (\(Writer key) -> liftIO $ modifyMVar_ printVar $ \n -> do
      --       putText $ fold (replicate n "| ") <> "fetching " <> show key
      --       return $ n + 1)
      --     (\_ _ -> liftIO $ modifyMVar_ printVar $ \n -> do
      --       putText $ fold (replicate (n - 1) "| ") <> "*"
      --       return $ n - 1)
      writeErrors :: Writer TaskKind Query a -> [Error] -> Task Query ()
      writeErrors (Writer key) errs = do
        errs' <- mapM (prettyError <=< Error.Hydrated.fromError) errs
        liftIO $
          atomicModifyIORef (_errorsVar state) $
            (, ()) . if null errs' then DMap.delete key else DMap.insert key (Const errs')

      rules :: Rules Query
      rules =
        memoise (_startedVar state) $
        trackReverseDependencies (_reverseDependenciesVar state) $
        verifyTraces
          (_tracesVar state)
          (\query value -> do
            hashed <- liftIO $ readIORef $ _hashesVar state
            case DMap.lookup query hashed of
              Just h ->
                pure h

              Nothing -> do
                let
                  h =
                    Const $ hashTagged query value
                liftIO $
                  atomicModifyIORef (_hashesVar state) $
                    (, ()) . DMap.insert query h
                pure h
          ) $
        traceFetch_ $
        writer writeErrors $
        Rules.rules sourceDirectories (HashSet.fromMap $ void files) readSourceFile_
    -- result <- Rock.runMemoisedTask (_startedVar state) rules task
    result <- Rock.runTask sequentially rules task
    started <- readIORef $ _startedVar state
    errorsMap <- case prune of
      Don'tPrune ->
        readIORef $ _errorsVar state

      Prune -> do
        atomicModifyIORef (_tracesVar state) $
          (, ()) . DMap.intersectionWithKey (\_ _ t -> t) started
        atomicModifyIORef (_errorsVar state) $ \errors -> do
          let
            errors' = DMap.intersectionWithKey (\_ _ e -> e) started errors
          (errors', errors')
    let
      errors = do
        (_ DMap.:=> Const errs) <- DMap.toList errorsMap
        errs
    pure (result, errors)
  where
    handleEx m =
      m `catch` \e -> do
        Text.hPutStrLn stderr $ "exception! " <> show (e :: SomeException)
        panic $ show e

-------------------------------------------------------------------------------

checkAll :: Task Query ()
checkAll = do
  filePaths <- fetch $ Query.InputFiles
  parsedFiles <- forM (HashSet.toList filePaths) $ fetch . Query.ParsedFile
  forM_ parsedFiles $ \(module_, _, defs) -> do
    let
      names =
        HashSet.fromList $
          Name.Qualified module_ . fst . snd <$> defs
    forM_ (HashSet.toList names) $ \name -> do
      void $ fetch $ Query.ElaboratedType name
      fetch $ Query.ElaboratedDefinition name
