{-# language OverloadedStrings #-}
module Readback where

import Protolude hiding (IntMap, Seq, force, evaluate)

import qualified Domain
import qualified Environment
import qualified Evaluation
import Index
import Monad
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

-------------------------------------------------------------------------------

readback :: Domain.Environment v -> Domain.Value -> M (Syntax.Term v)
readback env value =
  case value of
    Domain.Neutral hd spine -> do
      hd' <- readbackHead env hd
      readbackSpine hd' spine

    Domain.Glued hd spine value' -> do
      maybeHead <- readbackMaybeHead env hd
      case maybeHead of
        Nothing -> do
          value'' <- force value'
          readback env value''

        Just hd' ->
          readbackSpine hd' spine

    Domain.Lam name type_ plicity closure ->
      Syntax.Lam name <$> readback env type_ <*> pure plicity <*> readbackClosure env closure

    Domain.Pi name type_ plicity closure ->
      Syntax.Pi name <$> readback env type_ <*> pure plicity <*> readbackClosure env closure

    Domain.Fun source domain ->
      Syntax.Fun <$> readback env source <*> readback env domain

    Domain.Case scrutinee (Domain.Branches env' branches defaultBranch) -> do
      scrutinee' <- readback env scrutinee
      branches' <- forM branches $ readbackBranch env env'
      defaultBranch' <- forM defaultBranch $ \branch -> do
        branch' <- Evaluation.evaluate env' branch
        readback env branch'
      pure $ Syntax.Case scrutinee' branches' defaultBranch'
  where
    readbackSpine =
      foldM $ \fun (plicity, arg) -> do
        arg' <- readback env arg
        pure $ Syntax.App fun plicity arg'

readbackClosure :: Domain.Environment v -> Domain.Closure -> M (Scope Syntax.Term v)
readbackClosure env closure = do
  (env', v) <- Environment.extend env
  closure' <- Evaluation.evaluateClosure closure $ Domain.var v
  readback env' closure'

readbackHead :: Domain.Environment v -> Domain.Head -> M (Syntax.Term v)
readbackHead env hd = do
  maybeTerm <- readbackMaybeHead env hd
  case maybeTerm of
    Nothing ->
      panic "readbackHead: Nothing"

    Just term ->
      pure term

readbackMaybeHead :: Domain.Environment v -> Domain.Head -> M (Maybe (Syntax.Term v))
readbackMaybeHead env hd =
  case hd of
    Domain.Var v ->
      case (Environment.lookupVarIndex v env, Environment.lookupVarValue v env) of
        (Just i, _) ->
          pure $ Just $ Syntax.Var i

        (Nothing, Just value) -> do
          term <- readback env value
          pure $ Just term

        (Nothing, Nothing) ->
          pure Nothing

    Domain.Global g ->
      pure $ Just $ Syntax.Global g

    Domain.Con c ->
      pure $ Just $ Syntax.Con c

    Domain.Meta m ->
      pure $ Just $ Syntax.Meta m

readbackBranch
  :: Domain.Environment v
  -> Domain.Environment v'
  -> Telescope Syntax.Type Syntax.Term v'
  -> M (Telescope Syntax.Type Syntax.Term v)
readbackBranch outerEnv innerEnv tele =
  case tele of
    Telescope.Empty term -> do
      value <- Evaluation.evaluate innerEnv term
      term' <- readback outerEnv value
      pure $ Telescope.Empty term'

    Telescope.Extend name source plicity tele' -> do
      source' <- Evaluation.evaluate innerEnv source
      source'' <- readback outerEnv source'
      (outerEnv', var) <- Environment.extend outerEnv
      let
        innerEnv' =
          Environment.extendVar innerEnv var
      tele'' <- readbackBranch outerEnv' innerEnv' tele'
      pure $ Telescope.Extend name source'' plicity tele''
