{-# language OverloadedStrings #-}
module Core.Readback where

import Protolude hiding (IntMap, Seq, head, force, evaluate)

import Core.Bindings (Bindings)
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Core.Domain as Domain
import qualified Environment
import qualified Core.Evaluation as Evaluation
import Index
import Monad
import qualified Core.Syntax as Syntax
import Telescope (Telescope)
import qualified Telescope

-------------------------------------------------------------------------------

readback :: Domain.Environment v -> Domain.Value -> M (Syntax.Term v)
readback env value =
  case value of
    Domain.Neutral head spine -> do
      head' <- readbackHead env head
      readbackSpine env head' spine

    Domain.Con con args ->
      Syntax.apps (Syntax.Con con) <$> mapM (mapM $ readback env) args

    Domain.Lit lit ->
      pure $ Syntax.Lit lit

    Domain.Glued head spine value' -> do
      maybeHead <- readbackMaybeHead env head
      case maybeHead of
        Nothing -> do
          value'' <- force value'
          readback env value''

        Just head' ->
          readbackSpine env head' spine

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
          Syntax.LiteralBranches <$> OrderedHashMap.forMUnordered literalBranches (mapM $ \branch -> do
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

readbackHead :: Domain.Environment v -> Domain.Head -> M (Syntax.Term v)
readbackHead env head = do
  maybeTerm <- readbackMaybeHead env head
  case maybeTerm of
    Nothing ->
      panic "readbackHead: Nothing"

    Just term ->
      pure term

readbackMaybeHead :: Domain.Environment v -> Domain.Head -> M (Maybe (Syntax.Term v))
readbackMaybeHead env head =
  case head of
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

    Domain.Meta m ->
      pure $ Just $ Syntax.Meta m

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
      let
        innerEnv' =
          Environment.extendVar innerEnv var
      tele'' <- readbackConstructorBranch outerEnv' innerEnv' tele'
      pure $ Telescope.Extend name domain'' plicity tele''
