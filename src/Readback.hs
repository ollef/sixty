{-# language OverloadedStrings #-}
{-# language PackageImports #-}
module Readback where

import Protolude hiding (IntMap, Seq, force, evaluate)

import "this" Data.IntMap (IntMap)
import qualified Data.Tsil as Tsil
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
  , values :: IntMap Var (Lazy Domain.Value)
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

lookupVarValue :: Var -> Environment v -> Maybe (Lazy Domain.Type)
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
    Domain.Neutral hd spine ->
      readbackNeutral env hd spine

    Domain.Glued hd spine _ ->
      readbackNeutral env hd spine

    Domain.Lam name type_ plicity closure -> do
      type' <- force type_
      Syntax.Lam name <$> readback env type' <*> pure plicity <*> readbackClosure env closure

    Domain.Pi name type_ plicity closure -> do
      type' <- force type_
      Syntax.Pi name <$> readback env type' <*> pure plicity <*> readbackClosure env closure

    Domain.Fun source domain -> do
      source' <- force source
      domain' <- force domain
      Syntax.Fun <$> readback env source' <*> readback env domain'

    Domain.Case scrutinee (Domain.Branches env' branches) -> do
      scrutinee' <- readback env scrutinee
      branches' <- forM branches $ \(Syntax.Branch constr tele) ->
        Syntax.Branch constr <$> readbackBranch env env' tele
      pure $ Syntax.Case scrutinee' branches'

readbackClosure :: Environment v -> Domain.Closure -> M (Scope Syntax.Term v)
readbackClosure env closure = do
  (env', v) <- extend env

  closure' <- Evaluation.evaluateClosure closure $ Lazy $ pure $ Domain.var v
  readback env' closure'

readbackNeutral :: Environment v -> Domain.Head -> Domain.Spine -> M (Syntax.Term v)
readbackNeutral env hd spine =
  case spine of
    Tsil.Empty ->
      readbackHead env hd

    spine' Tsil.:> (plicity, arg) -> do
      arg' <- force arg
      Syntax.App <$> readbackNeutral env hd spine' <*> pure plicity <*> readback env arg'

readbackHead :: Environment v -> Domain.Head -> M (Syntax.Term v)
readbackHead env hd =
  case hd of
    Domain.Var v ->
      case (lookupVarIndex v env, lookupVarValue v env) of
        (Just i, _) ->
          pure $ Syntax.Var i

        (Nothing, Just value) -> do
          value' <- force value
          readback env value'

        (Nothing, Nothing) ->
          panic $ "readbackHead: Scoping error (" <> show v <> ")"

    Domain.Global g ->
      pure $ Syntax.Global g

    Domain.Con c ->
      pure $ Syntax.Con c

    Domain.Meta m ->
      pure $ Syntax.Meta m

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
