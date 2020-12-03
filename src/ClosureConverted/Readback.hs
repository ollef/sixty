{-# language OverloadedStrings #-}
module ClosureConverted.Readback where

import Protolude hiding (IntMap, Seq, head, force, evaluate)

import qualified ClosureConversion
import qualified ClosureConverted.Domain as Domain
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Syntax as Syntax
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Environment
import Index
import Monad
import Name (Name)
import Telescope (Telescope)
import qualified Telescope

readback :: Domain.Environment v -> Domain.Value -> M (Syntax.Term v)
readback env value =
  case value of
    Domain.Neutral head spine ->
      case head of
        Domain.Global global -> do
          case Domain.groupSpine spine of
            Domain.GroupedApps args : groupedSpine -> do
              args' <- mapM (readback env) args
              globalApplication <- ClosureConversion.convertGlobal global args'
              readbackGroupedSpine env globalApplication groupedSpine

            groupedSpine -> do
              global' <- ClosureConversion.convertGlobal global mempty
              readbackGroupedSpine env global' groupedSpine

        Domain.Var var -> do
          let
            term =
              Syntax.Var $ fromMaybe (panic $ "ClosureConverted.Readback var " <> show var) $ Environment.lookupVarIndex var env

          readbackGroupedSpine env term $ Domain.groupSpine spine

    Domain.Con con params args ->
      Syntax.Con con <$> mapM (readback env) params <*> mapM (readback env) args

    Domain.Lit lit ->
      pure $ Syntax.Lit lit

    Domain.Pi name type_ closure ->
      Syntax.Pi name <$> readback env type_ <*> readbackClosure env closure

    Domain.Function tele ->
      pure $ Syntax.Function tele

readbackGroupedElimination :: Domain.Environment v -> Syntax.Term v -> Domain.GroupedElimination -> M (Syntax.Term v)
readbackGroupedElimination env eliminee elimination =
  case elimination of
    Domain.GroupedApps args -> do
      args' <- mapM (readback env) args
      ClosureConversion.applyArgs args' $ pure eliminee

    Domain.GroupedCase (Domain.Branches env' branches defaultBranch) -> do
      branches' <- case branches of
        Syntax.ConstructorBranches constructorTypeName constructorBranches ->
          Syntax.ConstructorBranches constructorTypeName <$> OrderedHashMap.forMUnordered constructorBranches (readbackConstructorBranch env env')

        Syntax.LiteralBranches literalBranches ->
          Syntax.LiteralBranches <$> OrderedHashMap.forMUnordered literalBranches (\branch -> do
            branchValue <- Evaluation.evaluate env' branch
            readback env branchValue
          )
      defaultBranch' <- forM defaultBranch $ \branch -> do
        branch' <- Evaluation.evaluate env' branch
        readback env branch'
      pure $ Syntax.Case eliminee branches' defaultBranch'

readbackGroupedSpine :: Foldable f => Domain.Environment v -> Syntax.Term v -> f Domain.GroupedElimination -> M (Syntax.Term v)
readbackGroupedSpine =
  foldlM . readbackGroupedElimination

readbackConstructorBranch
  :: Domain.Environment v
  -> Domain.Environment v'
  -> Telescope Name Syntax.Type Syntax.Term v'
  -> M (Telescope Name Syntax.Type Syntax.Term v)
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

readbackClosure :: Domain.Environment v -> Domain.Closure -> M (Scope Syntax.Term v)
readbackClosure env closure = do
  (env', v) <- Environment.extend env
  closure' <- Evaluation.evaluateClosure closure $ Domain.var v
  readback env' closure'
