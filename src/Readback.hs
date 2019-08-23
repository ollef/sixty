{-# language OverloadedStrings #-}
{-# language PackageImports #-}
module Readback where

import Protolude hiding (IntMap, Seq, force, evaluate)

import "this" Data.IntMap (IntMap)
import qualified Domain
import qualified Evaluation
import Index
import qualified Index.Map
import qualified Index.Map as Index
import Monad
import qualified "this" Data.IntMap as IntMap
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var

-------------------------------------------------------------------------------
-- Readback environments

data Environment v = Environment
  { indices :: Index.Map v Var
  , values :: IntMap Var Domain.Value
  }

empty :: Environment Void
empty = Environment
  { indices = Index.Map.Empty
  , values = mempty
  }

extend
  :: Environment v
  -> M (Environment (Succ v), Var)
extend env = do
  var <- freshVar
  pure
    ( extendVar env var
    , var
    )

extendVar
  :: Environment v
  -> Var
  -> Environment (Succ v)
extendVar env var =
  env
    { indices = indices env Index.Map.:> var
    }

lookupVarIndex :: Var -> Environment v -> Maybe (Index v)
lookupVarIndex var context =
  Index.Map.elemIndex var (indices context)

lookupIndexVar :: Index v -> Environment v -> Var
lookupIndexVar index context =
  Index.Map.index (indices context) index

lookupVarValue :: Var -> Environment v -> Maybe Domain.Type
lookupVarValue var context =
  IntMap.lookup var (values context)

fromEvaluationEnvironment :: Domain.Environment v -> Environment v
fromEvaluationEnvironment env =
  -- TODO merge with evaluation environment?
  Environment
    { indices = Domain.indices env
    , values = Domain.values env
    }

-------------------------------------------------------------------------------

readback :: Environment v -> Domain.Value -> M (Syntax.Term v)
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

readbackClosure :: Environment v -> Domain.Closure -> M (Scope Syntax.Term v)
readbackClosure env closure = do
  (env', v) <- extend env
  closure' <- Evaluation.evaluateClosure closure $ Domain.var v
  readback env' closure'

readbackHead :: Environment v -> Domain.Head -> M (Syntax.Term v)
readbackHead env hd = do
  maybeTerm <- readbackMaybeHead env hd
  case maybeTerm of
    Nothing ->
      panic "readbackHead: Nothing"

    Just term ->
      pure term

readbackMaybeHead :: Environment v -> Domain.Head -> M (Maybe (Syntax.Term v))
readbackMaybeHead env hd =
  case hd of
    Domain.Var v ->
      case (lookupVarIndex v env, lookupVarValue v env) of
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
  :: Environment v
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
      (outerEnv', var) <- extend outerEnv
      let
        innerEnv' =
          Domain.extendVar innerEnv var
      tele'' <- readbackBranch outerEnv' innerEnv' tele'
      pure $ Telescope.Extend name source'' plicity tele''
