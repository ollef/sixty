{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
module Unification where

import Protolude hiding (force, check, evaluate)

import qualified Builtin
import Context (Context)
import qualified Context
import Data.IntSequence (IntSeq)
import qualified Data.IntSequence as IntSeq
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Error
import qualified Evaluation
import Extra
import Index
import qualified Index.Map as Index
import qualified Meta
import Monad
import Plicity
import qualified Readback
import Readback (readback)
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var

tryUnify :: Context v -> Domain.Value -> Domain.Value -> M (Syntax.Term v -> Syntax.Term v)
tryUnify context value1 value2 = do
  success <- Context.try_ context $ unify context value1 value2
  if success then
    pure identity
  else do
    type_ <- Readback.readback (Context.toReadbackEnvironment context) value2
    pure $ const $ Syntax.App (Syntax.Global Builtin.fail) Explicit type_

unify :: Context v -> Domain.Value -> Domain.Value -> M ()
unify context value1 value2 = do
  value1' <- Context.forceHead context value1
  value2' <- Context.forceHead context value2
  case (value1', value2') of
    -- Both metas
    (Domain.Neutral (Domain.Meta metaIndex1) spine1, Domain.Neutral (Domain.Meta metaIndex2) spine2) -> do
      spine1' <- mapM ((force >=> Context.forceHead context) . snd) spine1
      spine2' <- mapM ((force >=> Context.forceHead context) . snd) spine2
      if metaIndex1 == metaIndex2 then do
        -- If the same metavar is applied to two different lists of unknown
        -- variables its solution must not mention any variables at
        -- positions where the lists differ.
        let
          keep = Tsil.zipWith shouldKeepMetaArgument spine1' spine2'

        if and keep then
          Tsil.zipWithM_ (unify context) spine1' spine2'

        else
          pruneMeta context metaIndex1 keep

      else do
        let
          spine1Vars = traverse Domain.singleVarView spine1'
          spine2Vars = traverse Domain.singleVarView spine2'

        case (spine1Vars, spine2Vars) of
          (Just vars1, _)
            | unique vars1 ->
              solve context metaIndex1 vars1 value2'

          (_, Just vars2)
            | unique vars2 ->
              solve context metaIndex2 vars2 value1'

          _ ->
            can'tUnify

    -- Same heads
    (Domain.Neutral head1 spine1, Domain.Neutral head2 spine2)
      | head1 == head2 ->
        Tsil.zipWithM_ (\(_, v1) (_, v2) -> unifyForce context v1 v2) spine1 spine2

    (Domain.Lam name1 type1 plicity1 closure1, Domain.Lam _ type2 plicity2 closure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 type1 closure1 type2 closure2

    (Domain.Pi name1 source1 plicity1 domainClosure1, Domain.Pi _ source2 plicity2 domainClosure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 source1 domainClosure1 source2 domainClosure2

    (Domain.Pi name1 source1 Explicit domainClosure1, Domain.Fun source2 domain2) -> do
      unifyForce context source2 source1

      (context', var) <- Context.extendUnnamed context name1 source1
      let
        lazyVar = Lazy $ pure $ Domain.var var

      domain1 <- Evaluation.evaluateClosure domainClosure1 lazyVar
      domain2' <- force domain2
      unify context' domain1 domain2'

    (Domain.Fun source1 domain1, Domain.Pi name2 source2 Explicit domainClosure2) -> do
      unifyForce context source2 source1

      (context', var) <- Context.extendUnnamed context name2 source2
      let
        lazyVar = Lazy $ pure $ Domain.var var

      domain1' <- force domain1
      domain2 <- Evaluation.evaluateClosure domainClosure2 lazyVar
      unify context' domain1' domain2

    (Domain.Fun source1 domain1, Domain.Fun source2 domain2) -> do
      unifyForce context source2 source1
      unifyForce context domain1 domain2

    -- Eta expand
    (Domain.Lam name1 type1 plicity1 closure1, v2) -> do
      (context', var) <- Context.extendUnnamed context name1 type1
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 lazyVar
      body2 <- Evaluation.apply v2 plicity1 lazyVar

      unify context' body1 body2

    (v1, Domain.Lam name2 type2 plicity2 closure2) -> do
      (context', var) <- Context.extendUnnamed context name2 type2
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- Evaluation.apply v1 plicity2 lazyVar
      body2 <- Evaluation.evaluateClosure closure2 lazyVar

      unify context' body1 body2

    -- Metas
    (Domain.Neutral (Domain.Meta metaIndex1) spine1, v2) -> do
      spine1' <- mapM ((force >=> Context.forceHead context) . snd) spine1
      case traverse Domain.singleVarView spine1' of
        Just vars1
          | unique vars1 ->
            solve context metaIndex1 vars1 v2

        _ ->
          can'tUnify

    (v1, Domain.Neutral (Domain.Meta metaIndex2) spine2) -> do
      spine2' <- mapM ((force >=> Context.forceHead context) . snd) spine2
      case traverse Domain.singleVarView spine2' of
        Just vars2
          | unique vars2 ->
          solve context metaIndex2 vars2 v1

        _ ->
          can'tUnify

    _ ->
      can'tUnify

  where
    unifyForce sz lazyValue1 lazyValue2 = do
      v1 <- force lazyValue1
      v2 <- force lazyValue2
      unify sz v1 v2

    unifyAbstraction name type1 closure1 type2 closure2 = do
      unifyForce context type1 type2

      (context', var) <- Context.extendUnnamed context name type1
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 lazyVar
      body2 <- Evaluation.evaluateClosure closure2 lazyVar
      unify context' body1 body2

    can'tUnify =
      throwError Error.TypeMismatch

shouldKeepMetaArgument :: Domain.Value -> Domain.Value -> Bool
shouldKeepMetaArgument value1 value2 =
  case (value1, value2) of
    (Domain.Neutral (Domain.Var var1) Tsil.Empty, Domain.Neutral (Domain.Var var2) Tsil.Empty) ->
      var1 == var2

    (Domain.Neutral (Domain.Var _) Tsil.Empty, _) ->
      not $ simpleNonVar value2

    (_, Domain.Neutral (Domain.Var _) Tsil.Empty) ->
      not $ simpleNonVar value1

    _ ->
      True

  where
    simpleNonVar value =
      case value of
        Domain.Neutral hd Tsil.Empty ->
          case hd of
            Domain.Var _ ->
              False

            _ ->
              True

        _ ->
          False

-- | Solve `meta = \vars. value`.
solve :: Context v -> Meta.Index -> Tsil Var -> Domain.Value -> M ()
solve context meta vars value = do
  term <- checkSolution context meta (IntSeq.fromTsil vars) value
  Context.solveMeta context meta term

-- | Occurs check, scope check, prune, and read back the solution at the same
-- time.
checkSolution
  :: Context v
  -> Meta.Index
  -> IntSeq Var
  -> Domain.Value
  -> M (Syntax.Term Void)
checkSolution outerContext meta vars value = do
  solution <-
    checkInnerSolution
      outerContext
      meta
      Readback.Environment
        { indices = Index.Map vars
        , values = Context.values outerContext
        }
      value
  addAndCheckLambdas outerContext meta vars solution

addAndCheckLambdas
  :: Context v
  -> Meta.Index
  -> IntSeq Var
  -> Syntax.Term v'
  -> M (Syntax.Term v')
addAndCheckLambdas outerContext meta vars term =
  case vars of
    IntSeq.Empty ->
      pure term

    vars' IntSeq.:> var -> do
      let
        name =
          Context.lookupVarName var outerContext
        type_ =
          Context.lookupVarType var outerContext

      type' <- force type_
      type'' <-
        checkInnerSolution
          outerContext
          meta
          Readback.Environment
            { indices = Index.Map vars'
            , values = Context.values outerContext
            }
          type'
      let
        term' = Syntax.Lam name type'' Explicit (Syntax.succ term)
      addAndCheckLambdas outerContext meta vars' term'

checkInnerSolution
  :: Context v
  -> Meta.Index
  -> Readback.Environment v'
  -> Domain.Value
  -> M (Syntax.Term v')
checkInnerSolution outerContext occurs env value = do
  value' <- Context.forceHead outerContext value
  case value' of
    Domain.Neutral hd@(Domain.Meta i) spine -> do
      spine' <- mapM ((force >=> Context.forceHead outerContext) . snd) spine
      case traverse Domain.singleVarView spine' of
        Just vars
          | allowedVars <- map (\v -> isJust (Readback.lookupVarIndex v env)) vars
          , any not allowedVars
          -> do
            pruneMeta outerContext i allowedVars
            checkInnerSolution outerContext occurs env value'

        _ ->
          checkInnerNeutral outerContext occurs env hd spine

    Domain.Neutral hd spine ->
      checkInnerNeutral outerContext occurs env hd spine

    Domain.Lam name type_ plicity closure -> do
      type' <- force type_
      Syntax.Lam name
        <$> checkInnerSolution outerContext occurs env type'
        <*> pure plicity
        <*> checkInnerClosure outerContext occurs env closure

    Domain.Pi name type_ plicity closure -> do
      type' <- force type_
      Syntax.Pi name
        <$> checkInnerSolution outerContext occurs env type'
        <*> pure plicity
        <*> checkInnerClosure outerContext occurs env closure

    Domain.Fun source domain -> do
      source' <- force source
      domain' <- force domain
      Syntax.Fun
        <$> checkInnerSolution outerContext occurs env source'
        <*> checkInnerSolution outerContext occurs env domain'

    Domain.Case scrutinee (Domain.Branches env' branches) -> do
      scrutinee' <- checkInnerSolution outerContext occurs env scrutinee
      branches' <- forM branches $ \(Syntax.Branch constr tele) ->
        Syntax.Branch constr <$> checkInnerBranch outerContext occurs env env' tele
      pure $ Syntax.Case scrutinee' branches'

checkInnerBranch
  :: Context outer
  -> Meta.Index
  -> Readback.Environment v
  -> Domain.Environment v'
  -> Telescope Syntax.Type Syntax.Term v'
  -> M (Telescope Syntax.Type Syntax.Term v)
checkInnerBranch outerContext occurs outerEnv innerEnv tele =
  case tele of
    Telescope.Empty term -> do
      value <- Evaluation.evaluate innerEnv term
      term' <- checkInnerSolution outerContext occurs outerEnv value
      pure $ Telescope.Empty term'

    Telescope.Extend name source plicity tele' -> do
      source' <- Evaluation.evaluate innerEnv source
      source'' <- checkInnerSolution outerContext occurs outerEnv source'
      (outerEnv', var) <- Readback.extend outerEnv
      let
        innerEnv' =
          Domain.extendVar innerEnv var
      tele'' <- checkInnerBranch outerContext occurs outerEnv' innerEnv' tele'
      pure $ Telescope.Extend name source'' plicity tele''

checkInnerClosure
  :: Context v
  -> Meta.Index
  -> Readback.Environment v'
  -> Domain.Closure
  -> M (Scope Syntax.Term v')
checkInnerClosure outerContext occurs env closure = do
  (env', v) <- Readback.extend env

  closure' <- Evaluation.evaluateClosure closure $ Lazy $ pure $ Domain.var v
  checkInnerSolution outerContext occurs env' closure'

checkInnerNeutral
  :: Context v
  -> Meta.Index
  -> Readback.Environment v'
  -> Domain.Head
  -> Domain.Spine
  -> M (Syntax.Term v')
checkInnerNeutral outerContext occurs env hd spine =
  case spine of
    Tsil.Empty ->
      checkInnerHead occurs env hd

    spine' Tsil.:> (plicity, arg) -> do
      arg' <- force arg
      Syntax.App
        <$> checkInnerNeutral outerContext occurs env hd spine'
        <*> pure plicity
        <*> checkInnerSolution outerContext occurs env arg'

checkInnerHead
  :: Meta.Index
  -> Readback.Environment v
  -> Domain.Head
  -> M (Syntax.Term v)
checkInnerHead occurs env hd =
  case hd of
    Domain.Var v ->
      case Readback.lookupVarIndex v env of
        Nothing ->
          throwError Error.TypeMismatch

        Just i ->
          pure $ Syntax.Var i

    Domain.Global g ->
      pure $ Syntax.Global g

    Domain.Con g ->
      pure $ Syntax.Con g

    Domain.Meta m
      | m == occurs ->
        throwError Error.OccursCheck

      | otherwise ->
        pure $ Syntax.Meta m

pruneMeta
  :: Context v
  -> Meta.Index
  -> Tsil Bool
  -> M ()
pruneMeta context meta allowedArgs = do
  solution <- Context.lookupMeta meta context
  -- putText $ "pruneMeta " <> show meta
  -- putText $ "pruneMeta " <> show allowedArgs
  case solution of
    Meta.Unsolved metaType _ -> do
      -- putText $ show metaType
      metaType' <-
        Evaluation.evaluate
          (Domain.empty $ Context.scopeKey context)
          metaType
      solution' <-
        go
          (toList allowedArgs)
          (Context.emptyFrom context)
          metaType'
      Context.solveMeta context meta solution'

    Meta.Solved {} ->
      panic "pruneMeta already solved"

  where
    go :: [Bool] -> Context v -> Domain.Type -> M (Syntax.Term v)
    go alloweds context' type_ =
      case alloweds of
        [] -> do
          v <- Context.newMeta type_ context'
          Readback.readback (Context.toReadbackEnvironment context') v

        allowed:alloweds' ->
          case type_ of
            Domain.Fun source domain -> do
              source' <- force source
              source'' <-
                Readback.readback
                  (Context.toReadbackEnvironment context')
                  source'
              (context'', _) <-
                if allowed then
                  Context.extendUnnamed context' "x" source
                else
                  Context.extendUnnamedDef
                    context'
                    "x"
                    (Lazy $ throwError Error.TypeMismatch)
                    source
              domain' <- force domain
              body <- go alloweds' context'' domain'
              pure $ Syntax.Lam "x" source'' Explicit body

            Domain.Pi name source plicity domainClosure -> do
              (context'', v) <-
                if allowed then
                  Context.extend context' name source
                else
                  Context.extendUnnamedDef
                    context'
                    name
                    (Lazy $ throwError Error.TypeMismatch)
                    source
              domain <-
                Evaluation.evaluateClosure
                  domainClosure
                  (Lazy $ pure $ Domain.var v)
              source' <- force source
              source'' <-
                Readback.readback
                  (Context.toReadbackEnvironment context')
                  source'
              body <- go alloweds' context'' domain
              pure $ Syntax.Lam name source'' plicity body

            _ -> panic "pruneMeta wrong type"
