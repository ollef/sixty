{-# LANGUAGE OverloadedStrings #-}

module Core.Readback where

import Core.Bindings (Bindings)
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Syntax as Syntax
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Environment
import Index
import Monad
import Protolude hiding (IntMap, Seq, evaluate, force, head)
import Telescope (Telescope)
import qualified Telescope

-------------------------------------------------------------------------------

readback :: Domain.Environment v -> Domain.Value -> M (Syntax.Term v)
readback env value =
  case value of
    Domain.Neutral head spine ->
      case head of
        Domain.Var v ->
          case (Environment.lookupVarIndex v env, Environment.lookupVarValue v env) of
            (Just i, _) ->
              readbackSpine env (Syntax.Var i) spine
            -- This case can happen because of pruning and pattern matching elaboration:
            -- 1. Pattern matching elaboration can give a value to a variable that previously didn't have one
            -- 2. During pruning, we will remove variables from scope and try to readback.
            (Nothing, Just varValue) -> do
              head' <- readback env varValue
              readbackSpine env head' spine
            (Nothing, Nothing) ->
              panic $ "readback neutral var " <> show v
        Domain.Global g ->
          readbackSpine env (Syntax.Global g) spine
        Domain.Meta m ->
          readbackSpine env (Syntax.Meta m) spine
    Domain.Con con args ->
      Syntax.apps (Syntax.Con con) <$> mapM (mapM $ readback env) args
    Domain.Lit lit ->
      pure $ Syntax.Lit lit
    Domain.Glued head spine value' ->
      case head of
        Domain.Var v ->
          case Environment.lookupVarIndex v env of
            Just i ->
              readbackSpine env (Syntax.Var i) spine
            -- This can happen
            -- 1. because of pruning, where we create lazy variables with
            -- values that lazily throw exceptions when they're forced so we
            -- can detect whether a variable that can't be used is used.
            -- 2. when reading back a glued variable in an environment that
            -- doesn't bind the variable (e.g. the type of a let body in the
            -- outer scope).
            Nothing ->
              readback env value'
        Domain.Global g ->
          readbackSpine env (Syntax.Global g) spine
        Domain.Meta m ->
          readbackSpine env (Syntax.Meta m) spine
    Domain.Lazy lazyValue -> do
      value' <- force lazyValue
      readback env value'
    Domain.Lam binding type_ plicity closure ->
      Syntax.Lam binding <$> readback env type_ <*> pure plicity <*> readbackClosure env closure
    Domain.Pi binding type_ plicity closure ->
      Syntax.Pi binding <$> readback env type_ <*> pure plicity <*> readbackClosure env closure
    Domain.Fun domain plicity target ->
      Syntax.Fun <$> readback env domain <*> pure plicity <*> readback env target

readbackElimination :: Domain.Environment v -> Syntax.Term v -> Domain.Elimination -> M (Syntax.Term v)
readbackElimination env eliminee elimination =
  case elimination of
    Domain.App plicity arg -> do
      arg' <- readback env arg
      pure $ Syntax.App eliminee plicity arg'
    Domain.Case (Domain.Branches env' branches defaultBranch) -> do
      branches' <- case branches of
        Syntax.ConstructorBranches constructorTypeName constructorBranches ->
          Syntax.ConstructorBranches constructorTypeName <$> OrderedHashMap.forMUnordered constructorBranches (mapM $ readbackConstructorBranch env env')
        Syntax.LiteralBranches literalBranches ->
          Syntax.LiteralBranches
            <$> OrderedHashMap.forMUnordered
              literalBranches
              ( mapM $ \branch -> do
                  branchValue <- Evaluation.evaluate env' branch
                  readback env branchValue
              )
      defaultBranch' <- forM defaultBranch $ \branch -> do
        branch' <- Evaluation.evaluate env' branch
        readback env branch'
      pure $ Syntax.Case eliminee branches' defaultBranch'

readbackSpine :: Domain.Environment v -> Syntax.Term v -> Domain.Spine -> M (Syntax.Term v)
readbackSpine =
  Domain.foldlM . readbackElimination

readbackClosure :: Domain.Environment v -> Domain.Closure -> M (Scope Syntax.Term v)
readbackClosure env closure = do
  (env', v) <- Environment.extend env
  closure' <- Evaluation.evaluateClosure closure $ Domain.var v
  readback env' closure'

readbackConstructorBranch
  :: Domain.Environment v
  -> Domain.Environment v'
  -> Telescope Bindings Syntax.Type Syntax.Term v'
  -> M (Telescope Bindings Syntax.Type Syntax.Term v)
readbackConstructorBranch outerEnv innerEnv tele =
  case tele of
    Telescope.Empty term -> do
      value <- Evaluation.evaluate innerEnv term
      term' <- readback outerEnv value
      pure $ Telescope.Empty term'
    Telescope.Extend name domain plicity tele' -> do
      domain' <- Evaluation.evaluate innerEnv domain
      domain'' <- readback outerEnv domain'
      (outerEnv', var) <- Environment.extend outerEnv
      let innerEnv' =
            Environment.extendVar innerEnv var
      tele'' <- readbackConstructorBranch outerEnv' innerEnv' tele'
      pure $ Telescope.Extend name domain'' plicity tele''
