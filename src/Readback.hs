{-# language OverloadedStrings #-}
module Readback where

import Protolude hiding (Seq, force, evaluate)

import Data.IntSequence (IntSeq)
import qualified Data.IntSequence as IntSeq
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Evaluation
import Index
import Monad
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var

-------------------------------------------------------------------------------
-- Readback environments

newtype Environment v = Environment
  { vars :: IntSeq Var
  } deriving Show

empty :: Environment Void
empty = Environment
  { vars = mempty
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
    { vars = vars env IntSeq.:> var
    }

lookupVarIndex :: Var -> Environment v -> Maybe (Index v)
lookupVarIndex var context =
  case IntSeq.elemIndex var (vars context) of
    Nothing ->
      Nothing

    Just i ->
      Just (Index (IntSeq.length (vars context) - i - 1))

lookupIndexVar :: Index v -> Environment v -> Var
lookupIndexVar (Index i) context =
  IntSeq.index (vars context) (IntSeq.length (vars context) - i - 1)

fromEvaluationEnvironment :: Domain.Environment v -> Environment v
fromEvaluationEnvironment env =
  Environment
    { vars = Domain.vars env
    }

-------------------------------------------------------------------------------

readback :: Environment v -> Domain.Value -> M (Syntax.Term v)
readback env value =
  case value of
    Domain.Neutral hd spine ->
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
      case lookupVarIndex v env of
        Just i ->
          pure $ Syntax.Var i

        Nothing ->
          panic "readbackHead: Scoping error"

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
