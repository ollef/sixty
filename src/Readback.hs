{-# language OverloadedStrings #-}
module Readback where

import Protolude hiding (IntMap, Seq, head, force, evaluate)

import qualified Binding
import qualified Data.OrderedHashMap as OrderedHashMap
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
    Domain.Neutral head spine -> do
      head' <- readbackHead env head
      readbackSpine head' spine

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
          readbackSpine head' spine

    Domain.Lam name type_ plicity closure ->
      Syntax.Lam (Binding.Unspanned name) <$> readback env type_ <*> pure plicity <*> readbackClosure env closure

    Domain.Pi name type_ plicity closure ->
      Syntax.Pi (Binding.Unspanned name) <$> readback env type_ <*> pure plicity <*> readbackClosure env closure

    Domain.Fun domain plicity target ->
      Syntax.Fun <$> readback env domain <*> pure plicity <*> readback env target
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

    Domain.Case scrutinee (Domain.Branches env' branches defaultBranch) -> do
      scrutinee' <- readback env scrutinee
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
      pure $ Just $ Syntax.Case scrutinee' branches' defaultBranch'

readbackConstructorBranch
  :: Domain.Environment v
  -> Domain.Environment v'
  -> Telescope Syntax.Type Syntax.Term v'
  -> M (Telescope Syntax.Type Syntax.Term v)
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
