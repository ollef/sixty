{-# language OverloadedStrings #-}
module Readback where

import Protolude hiding (Seq, force, evaluate)

import qualified Domain
import qualified Evaluation
import Index
import Monad
import Data.IntSequence (IntSeq)
import qualified Data.IntSequence as IntSeq
import qualified Syntax
import qualified Data.Tsil as Tsil
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

    Domain.Lam name type_ closure -> do
      type' <- force type_
      Syntax.Lam name <$> readback env type' <*> readbackClosure env closure

    Domain.Pi name type_ closure -> do
      type' <- force type_
      Syntax.Pi name <$> readback env type' <*> readbackClosure env closure

    Domain.Fun source domain -> do
      source' <- force source
      domain' <- force domain
      Syntax.Fun <$> readback env source' <*> readback env domain'

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

    spine' Tsil.:> arg -> do
      arg' <- force arg
      Syntax.App <$> readbackNeutral env hd spine' <*> readback env arg'

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
