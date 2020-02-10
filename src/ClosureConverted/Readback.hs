{-# language OverloadedStrings #-}
module ClosureConverted.Readback where

import Protolude hiding (IntMap, Seq, head, force, evaluate)

import qualified ClosureConverted.Domain as Domain
import qualified ClosureConversion
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Syntax as Syntax
import qualified Environment
import Index
import Monad
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

readback :: Domain.Environment v -> Domain.Value -> M (Syntax.Term v)
readback env value =
  case value of
    Domain.Neutral head args -> do
      args' <- mapM (readback env) args
      case head of
        Domain.Var var -> do
          let
            term =
              Syntax.Var $ fromMaybe (panic "ClosureConverted.Readback var") $ Environment.lookupVarIndex var env

          ClosureConversion.applyArgs args' $ pure term

        Domain.Global global ->
          ClosureConversion.convertGlobal global args'

        Domain.Case scrutinee (Domain.Branches env' branches defaultBranch) ->
          ClosureConversion.applyArgs args' $ do
            scrutinee' <- readback env scrutinee
            branches' <- case branches of
              Syntax.ConstructorBranches constructorBranches ->
                Syntax.ConstructorBranches <$> forM constructorBranches (readbackConstructorBranch env env')

              Syntax.LiteralBranches literalBranches ->
                Syntax.LiteralBranches <$> forM literalBranches (\branch -> do
                  branchValue <- Evaluation.evaluate env' branch
                  readback env branchValue
                )
            defaultBranch' <- forM defaultBranch $ \branch -> do
              branch' <- Evaluation.evaluate env' branch
              readback env branch'
            pure $ Syntax.Case scrutinee' branches' defaultBranch'

    Domain.Con con params args ->
      Syntax.Con con <$> mapM (readback env) params <*> mapM (readback env) args

    Domain.Lit lit ->
      pure $ Syntax.Lit lit

    Domain.Pi name type_ closure ->
      Syntax.Pi name <$> readback env type_ <*> readbackClosure env closure

    Domain.Function tele ->
      pure $ Syntax.Function tele

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

readbackClosure :: Domain.Environment v -> Domain.Closure -> M (Scope Syntax.Term v)
readbackClosure env closure = do
  (env', v) <- Environment.extend env
  closure' <- Evaluation.evaluateClosure closure $ Domain.var v
  readback env' closure'
