{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
module Unification where

import Protolude hiding (force, check, evaluate)

import qualified Data.HashMap.Lazy as HashMap
import Rock

import {-# source #-} qualified Elaboration
import qualified Builtin
import Context (Context)
import qualified Context
import Data.IntSeq (IntSeq)
import qualified Data.IntSeq as IntSeq
import qualified Data.Tsil as Tsil
import Data.Tsil (Tsil)
import qualified Domain
import Environment (Environment(Environment))
import qualified Environment
import qualified Error
import qualified Evaluation
import Extra
import Flexibility (Flexibility)
import qualified Flexibility
import Index
import qualified Index.Map as Index
import qualified Meta
import Monad
import qualified Name
import qualified Binding
import Plicity
import qualified Query
import Readback (readback)
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var

tryUnify :: Context v -> Domain.Value -> Domain.Value -> M (Syntax.Term v -> Syntax.Term v)
tryUnify context value1 value2 = do
  success <- Context.try_ context $ unify context Flexibility.Rigid value1 value2
  if success then
    pure identity
  else do
    type_ <- Readback.readback (Context.toEnvironment context) value2
    pure $ const $ Syntax.App (Syntax.Global Builtin.fail) Explicit type_

tryUnifyD :: Context v -> Domain.Value -> Domain.Value -> M (Domain.Value -> Domain.Value)
tryUnifyD context value1 value2 = do
  success <- Context.try_ context $ unify context Flexibility.Rigid value1 value2
  pure $ if success then
    identity
  else
    const $ Domain.Neutral (Domain.Global Builtin.fail) $ pure (Explicit, value2)

unify :: Context v -> Flexibility -> Domain.Value -> Domain.Value -> M ()
unify context flexibility value1 value2 = do
  value1' <- Context.forceHeadGlue context value1
  value2' <- Context.forceHeadGlue context value2
  catchAndAdd $ case (value1', value2') of
    -- Both metas
    (Domain.Neutral (Domain.Meta metaIndex1) spine1, Domain.Neutral (Domain.Meta metaIndex2) spine2)
      | Flexibility.Rigid <- flexibility -> do
        spine1' <- mapM (Context.forceHead context . snd) spine1
        spine2' <- mapM (Context.forceHead context . snd) spine2
        if metaIndex1 == metaIndex2 then do
          -- If the same metavar is applied to two different lists of unknown
          -- variables its solution must not mention any variables at
          -- positions where the lists differ.
          let
            keep = Tsil.zipWith shouldKeepMetaArgument spine1' spine2'

          if and keep then
            unifySpines Flexibility.Flexible spine1 spine2

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
      | head1 == head2 -> do
        let
          flexibility' =
            max (Domain.headFlexibility head1) flexibility

        unifySpines flexibility' spine1 spine2

    (Domain.Lam name1 type1 plicity1 closure1, Domain.Lam _ type2 plicity2 closure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 type1 closure1 type2 closure2

    (Domain.Pi name1 source1 plicity1 domainClosure1, Domain.Pi _ source2 plicity2 domainClosure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 source1 domainClosure1 source2 domainClosure2

    (Domain.Pi name1 source1 Explicit domainClosure1, Domain.Fun source2 domain2) -> do
      unify context flexibility source2 source1
      (context', var) <- Context.extendUnnamed context name1 source1
      domain1 <- Evaluation.evaluateClosure domainClosure1 $ Domain.var var
      unify context' flexibility domain1 domain2

    (Domain.Fun source1 domain1, Domain.Pi name2 source2 Explicit domainClosure2) -> do
      unify context flexibility source2 source1
      (context', var) <- Context.extendUnnamed context name2 source2
      domain2 <- Evaluation.evaluateClosure domainClosure2 $ Domain.var var
      unify context' flexibility domain1 domain2

    (Domain.Fun source1 domain1, Domain.Fun source2 domain2) -> do
      unify context flexibility source2 source1
      unify context flexibility domain1 domain2

    -- Eta expand
    (Domain.Lam name1 type1 plicity1 closure1, v2) -> do
      (context', var) <- Context.extendUnnamed context name1 type1
      let
        varValue =
          Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 varValue
      body2 <- Evaluation.apply v2 plicity1 varValue

      unify context' flexibility body1 body2

    (v1, Domain.Lam name2 type2 plicity2 closure2) -> do
      (context', var) <- Context.extendUnnamed context name2 type2
      let
        varValue =
          Domain.var var

      body1 <- Evaluation.apply v1 plicity2 varValue
      body2 <- Evaluation.evaluateClosure closure2 varValue

      unify context' flexibility body1 body2

    -- Metas
    (Domain.Neutral (Domain.Meta metaIndex1) spine1, v2)
      | Flexibility.Rigid <- flexibility -> do
        spine1' <- mapM (Context.forceHead context . snd) spine1
        case traverse Domain.singleVarView spine1' of
          Just vars1
            | unique vars1 ->
              solve context metaIndex1 vars1 v2

          _ ->
            can'tUnify

    (v1, Domain.Neutral (Domain.Meta metaIndex2) spine2)
      | Flexibility.Rigid <- flexibility -> do
        spine2' <- mapM (Context.forceHead context . snd) spine2
        case traverse Domain.singleVarView spine2' of
          Just vars2
            | unique vars2 ->
            solve context metaIndex2 vars2 v1

          _ ->
            can'tUnify

    -- Case expressions
    (Domain.Case scrutinee1 branches1, Domain.Case scrutinee2 branches2) -> do
      unify context Flexibility.Flexible scrutinee1 scrutinee2
      unifyBranches context flexibility branches1 branches2

    (Domain.Case scrutinee@(Domain.Neutral (Domain.Meta meta) spine) branches, _)
      | Flexibility.Rigid <- flexibility -> do
        matches <- potentiallyMatchingBranches context value2' branches
        invertCase scrutinee meta spine matches

    (_, Domain.Case scrutinee@(Domain.Neutral (Domain.Meta meta) spine) branches)
      | Flexibility.Rigid <- flexibility -> do
        matches <- potentiallyMatchingBranches context value1' branches
        invertCase scrutinee meta spine matches

    -- Glued values
    (Domain.Glued head1 spine1 value1'', Domain.Glued head2 spine2 value2'')
      | head1 == head2 ->
        unifySpines Flexibility.Flexible spine1 spine2 `catchError` \_ ->
          unifyForce flexibility value1'' value2''

    (Domain.Glued _ _ value1'', _) -> do
      value1''' <- force value1''
      unify context flexibility value1''' value2'

    (_, Domain.Glued _ _ value2'') -> do
      value2''' <- force value2''
      unify context flexibility value1' value2'''

    _ ->
      can'tUnify

  where
    unifyForce flexibility' lazyValue1 lazyValue2 = do
      v1 <- force lazyValue1
      v2 <- force lazyValue2
      unify context flexibility' v1 v2

    unifySpines flexibility' =
      Tsil.zipWithM_ $ \(_, v1) (_, v2) -> unify context flexibility' v1 v2

    unifyAbstraction name type1 closure1 type2 closure2 = do
      unify context flexibility type1 type2

      (context', var) <- Context.extendUnnamed context name type1
      let
        varValue =
          Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 varValue
      body2 <- Evaluation.evaluateClosure closure2 varValue
      unify context' flexibility body1 body2

    invertCase scrutinee meta spine matches =
      case matches of
        [Just constr] -> do
          metaType <- instantiatedMetaType context meta spine
          appliedConstr <- fullyApplyToMetas context constr metaType
          unify context flexibility scrutinee appliedConstr
          unify context flexibility value1 value2

        _ ->
          can'tUnify

    catchAndAdd m =
      case flexibility of
        Flexibility.Rigid ->
          m `catchError` \err ->
            case err of
              Error.TypeMismatch stack -> do
                term1 <- Elaboration.readback context value1
                term2 <- Elaboration.readback context value2
                throwError $
                  Error.TypeMismatch $
                      stack Tsil.:>
                      ( Context.toPrettyableTerm context term1
                      , Context.toPrettyableTerm context term2
                      )

              Error.OccursCheck stack -> do
                term1 <- Elaboration.readback context value1
                term2 <- Elaboration.readback context value2
                throwError $
                  Error.OccursCheck $
                      stack Tsil.:>
                      ( Context.toPrettyableTerm context term1
                      , Context.toPrettyableTerm context term2
                      )

              _ ->
                throwError err

        Flexibility.Flexible ->
          m

    can'tUnify =
      throwError $ Error.TypeMismatch mempty

unifyBranches
  :: Context v
  -> Flexibility
  -> Domain.Branches
  -> Domain.Branches
  -> M ()
unifyBranches
  outerContext
  flexibility
  (Domain.Branches outerEnv1 branches1 defaultBranch1)
  (Domain.Branches outerEnv2 branches2 defaultBranch2) = do
    let
      branches =
        HashMap.intersectionWith (,) branches1 branches2

      missing1 =
        HashMap.difference branches1 branches

      missing2 =
        HashMap.difference branches2 branches
    unless (HashMap.null missing1 && HashMap.null missing2)
      can'tUnify

    forM_ branches $
      uncurry $ unifyTele outerContext outerEnv1 outerEnv2

    case (defaultBranch1, defaultBranch2) of
      (Just branch1, Just branch2) -> do
        branch1' <- Evaluation.evaluate outerEnv1 branch1
        branch2' <- Evaluation.evaluate outerEnv2 branch2
        unify outerContext flexibility branch1' branch2'

      (Nothing, Nothing) ->
        pure ()

      _ ->
        can'tUnify
  where
    unifyTele
      :: Context v
      -> Domain.Environment v1
      -> Domain.Environment v2
      -> Telescope Syntax.Type Syntax.Term v1
      -> Telescope Syntax.Type Syntax.Term v2
      -> M ()
    unifyTele context env1 env2 tele1 tele2 =
      case (tele1, tele2) of
        (Telescope.Extend binding1 type1 plicity1 tele1', Telescope.Extend _binding2 type2 plicity2 tele2')
          | plicity1 == plicity2 -> do
            type1' <- Evaluation.evaluate env1 type1
            type2' <- Evaluation.evaluate env2 type2
            unify context flexibility type1' type2'
            (context', var) <- Context.extendUnnamed context (Binding.toName binding1) type1'
            unifyTele
              context'
              (Environment.extendVar env1 var)
              (Environment.extendVar env2 var)
              tele1'
              tele2'

        (Telescope.Empty body1, Telescope.Empty body2) -> do
          body1' <- Evaluation.evaluate env1 body1
          body2' <- Evaluation.evaluate env2 body2
          unify context flexibility body1' body2'

        _ ->
          panic "unifyTele"

    can'tUnify =
      throwError $ Error.TypeMismatch mempty

-------------------------------------------------------------------------------
-- Case expression inversion

-- case scrutinee of
--   con1 vs1 -> con1' es1
--   con2 vs2 -> con2' es2
-- ==
-- con1' es1'
--
-- =>
--
-- scrutinee == con1 metas1
-- &&
-- con1' es1[metas1/vs1] == con1' es1'

potentiallyMatchingBranches
  :: Context v
  -> Domain.Value
  -> Domain.Branches
  -> M [Maybe Name.QualifiedConstructor]
potentiallyMatchingBranches outerContext resultValue (Domain.Branches outerEnv branches defaultBranch) = do
  defaultBranch' <- fmap (catMaybes . toList) $ forM defaultBranch $ \branch -> do
    isMatch <- branchMatches outerContext outerEnv $ Telescope.Empty branch
    pure $
      if isMatch then
        Just Nothing

      else
        Nothing

  branches' <- fmap catMaybes $ forM (HashMap.toList branches) $ \(constr, tele) -> do
    isMatch <- branchMatches outerContext outerEnv tele
    pure $
      if isMatch then
        Just $ Just constr

      else
        Nothing

  pure $ defaultBranch' <> branches'
  where
    branchMatches
      :: Context v
      -> Domain.Environment v'
      -> Telescope Syntax.Type Syntax.Term v'
      -> M Bool
    branchMatches context env tele =
      case tele of
        Telescope.Empty body -> do
          body' <- Evaluation.evaluate env body
          body'' <- Context.forceHead context body'
          case (body'', resultValue) of
            (Domain.Neutral (Domain.Meta _) _, _) ->
              pure True

            (Domain.Neutral hd1 _, Domain.Neutral hd2 _)
              | hd1 == hd2 ->
                pure True

            (Domain.Lam {}, Domain.Lam {}) ->
              pure True

            (Domain.Pi {}, Domain.Pi {}) ->
              pure True

            (Domain.Pi {}, Domain.Fun {}) ->
              pure True

            (Domain.Fun {}, Domain.Pi {}) ->
              pure True

            (Domain.Fun {}, Domain.Fun {}) ->
              pure True

            (Domain.Case _ branches', _) -> do
              matches <- potentiallyMatchingBranches context resultValue branches'
              pure $ not $ null matches

            _ ->
              pure False

        Telescope.Extend binding type_ _ tele' -> do
          type' <- Evaluation.evaluate env type_
          (context', var) <- Context.extendUnnamed context (Binding.toName binding) type'
          branchMatches context' (Environment.extendVar env var) tele'

instantiatedMetaType
  :: Context v
  -> Meta.Index
  -> Domain.Spine
  -> M Domain.Type
instantiatedMetaType context meta args = do
  solution <- Context.lookupMeta meta context
  case solution of
    Meta.Unsolved metaType _ -> do
      metaType' <-
        Evaluation.evaluate
          (Environment.empty $ Context.scopeKey context)
          metaType

      Context.instantiateType context metaType' $ toList args

    Meta.Solved {} ->
      panic "instantiatedMetaType already solved"

fullyApplyToMetas
  :: Context v
  -> Name.QualifiedConstructor
  -> Domain.Type
  -> M Domain.Value
fullyApplyToMetas context constr type_ = do
  type' <- Context.forceHead context type_
  case type' of
    Domain.Neutral (Domain.Global _typeName) typeArgs -> do
      constrType <- fetch $ Query.ConstructorType constr
      constrType' <-
        Evaluation.evaluate
          (Environment.empty $ Context.scopeKey context)
          (Syntax.fromVoid $ Telescope.fold Syntax.Pi constrType)
      instantiatedConstrType <- Context.instantiateType context constrType' $ toList typeArgs
      (metas, _) <- Elaboration.insertMetas context Elaboration.UntilTheEnd instantiatedConstrType
      pure $ Domain.Neutral (Domain.Con constr) $ typeArgs <> Tsil.fromList metas

    _ ->
      panic "fullyApplyToMetas"

-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- Solution checking and pruning

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
      Environment
        { scopeKey = Context.scopeKey outerContext
        , indices = Index.Map vars
        , values = Context.values outerContext
        }
      Flexibility.Rigid
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

      type' <-
        checkInnerSolution
          outerContext
          meta
          Environment
            { scopeKey = Context.scopeKey outerContext
            , indices = Index.Map vars'
            , values = Context.values outerContext
            }
          Flexibility.Rigid
          type_
      let
        term' = Syntax.Lam (Binding.Unspanned name) type' Explicit (Syntax.succ term)
      addAndCheckLambdas outerContext meta vars' term'

checkInnerSolution
  :: Context v
  -> Meta.Index
  -> Domain.Environment v'
  -> Flexibility
  -> Domain.Value
  -> M (Syntax.Term v')
checkInnerSolution outerContext occurs env flexibility value = do
  value' <- Context.forceHeadGlue outerContext value
  case value' of
    Domain.Neutral hd@(Domain.Meta i) spine
      | Flexibility.Rigid <- flexibility -> do
        spine' <- mapM (Context.forceHead outerContext . snd) spine
        case traverse Domain.singleVarView spine' of
          Just vars
            | allowedVars <- map (\v -> isJust (Environment.lookupVarIndex v env)) vars
            , any not allowedVars
            -> do
              pruneMeta outerContext i allowedVars
              checkInnerSolution outerContext occurs env flexibility value'

          _ ->
            checkInnerNeutral outerContext occurs env flexibility hd spine

    Domain.Neutral hd spine ->
      checkInnerNeutral outerContext occurs env flexibility hd spine

    Domain.Glued hd@(Domain.Global _) spine value'' ->
      checkInnerNeutral outerContext occurs env Flexibility.Flexible hd spine `catchError` \_ -> do
        value''' <- force value''
        checkInnerSolution outerContext occurs env flexibility value'''

    Domain.Glued _ _ value'' -> do
      value''' <- force value''
      checkInnerSolution outerContext occurs env flexibility value'''

    Domain.Lam name type_ plicity closure ->
      Syntax.Lam (Binding.Unspanned name)
        <$> checkInnerSolution outerContext occurs env flexibility type_
        <*> pure plicity
        <*> checkInnerClosure outerContext occurs env flexibility closure

    Domain.Pi name type_ plicity closure ->
      Syntax.Pi (Binding.Unspanned name)
        <$> checkInnerSolution outerContext occurs env flexibility type_
        <*> pure plicity
        <*> checkInnerClosure outerContext occurs env flexibility closure

    Domain.Fun source domain ->
      Syntax.Fun
        <$> checkInnerSolution outerContext occurs env flexibility source
        <*> checkInnerSolution outerContext occurs env flexibility domain

    Domain.Case scrutinee (Domain.Branches env' branches defaultBranch) -> do
      scrutinee' <- checkInnerSolution outerContext occurs env flexibility scrutinee
      branches' <- forM branches $
        checkInnerBranch outerContext occurs env env' flexibility
      defaultBranch' <- forM defaultBranch $ \branch -> do
        branch' <- Evaluation.evaluate env' branch
        checkInnerSolution outerContext occurs env flexibility branch'
      pure $ Syntax.Case scrutinee' branches' defaultBranch'

checkInnerBranch
  :: Context outer
  -> Meta.Index
  -> Domain.Environment v
  -> Domain.Environment v'
  -> Flexibility
  -> Telescope Syntax.Type Syntax.Term v'
  -> M (Telescope Syntax.Type Syntax.Term v)
checkInnerBranch outerContext occurs outerEnv innerEnv flexibility tele =
  case tele of
    Telescope.Empty term -> do
      value <- Evaluation.evaluate innerEnv term
      term' <- checkInnerSolution outerContext occurs outerEnv flexibility value
      pure $ Telescope.Empty term'

    Telescope.Extend name source plicity tele' -> do
      source' <- Evaluation.evaluate innerEnv source
      source'' <- checkInnerSolution outerContext occurs outerEnv flexibility source'
      (outerEnv', var) <- Environment.extend outerEnv
      let
        innerEnv' =
          Environment.extendVar innerEnv var
      tele'' <- checkInnerBranch outerContext occurs outerEnv' innerEnv' flexibility tele'
      pure $ Telescope.Extend name source'' plicity tele''

checkInnerClosure
  :: Context v
  -> Meta.Index
  -> Domain.Environment v'
  -> Flexibility
  -> Domain.Closure
  -> M (Scope Syntax.Term v')
checkInnerClosure outerContext occurs env flexibility closure = do
  (env', v) <- Environment.extend env
  closure' <- Evaluation.evaluateClosure closure $ Domain.var v
  checkInnerSolution outerContext occurs env' flexibility closure'

checkInnerNeutral
  :: Context v
  -> Meta.Index
  -> Domain.Environment v'
  -> Flexibility
  -> Domain.Head
  -> Domain.Spine
  -> M (Syntax.Term v')
checkInnerNeutral outerContext occurs env flexibility hd spine =
  case spine of
    Tsil.Empty ->
      checkInnerHead occurs env hd

    spine' Tsil.:> (plicity, arg) ->
      Syntax.App
        <$> checkInnerNeutral outerContext occurs env flexibility hd spine'
        <*> pure plicity
        <*> checkInnerSolution outerContext occurs env flexibility arg

checkInnerHead
  :: Meta.Index
  -> Domain.Environment v
  -> Domain.Head
  -> M (Syntax.Term v)
checkInnerHead occurs env hd =
  case hd of
    Domain.Var v ->
      case Environment.lookupVarIndex v env of
        Nothing ->
          throwError $ Error.TypeMismatch mempty

        Just i ->
          pure $ Syntax.Var i

    Domain.Global g ->
      pure $ Syntax.Global g

    Domain.Con g ->
      pure $ Syntax.Con g

    Domain.Meta m
      | m == occurs ->
        throwError $ Error.OccursCheck mempty

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
          (Environment.empty $ Context.scopeKey context)
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
          Readback.readback (Context.toEnvironment context') v

        allowed:alloweds' ->
          case type_ of
            Domain.Fun source domain -> do
              source' <-
                Readback.readback
                  (Context.toEnvironment context')
                  source
              (context'', _) <-
                if allowed then
                  Context.extendUnnamed context' "x" source
                else do
                  fakeVar <- freshVar
                  Context.extendUnnamedDef
                    context'
                    "x"
                    (Domain.Glued (Domain.Var fakeVar) mempty $ Lazy $ throwError $ Error.TypeMismatch mempty)
                    source
              body <- go alloweds' context'' domain
              pure $ Syntax.Lam "x" source' Explicit body

            Domain.Pi name source plicity domainClosure -> do
              (context'', v) <-
                if allowed then
                  Context.extendUnnamed context' name source
                else do
                  fakeVar <- freshVar
                  Context.extendUnnamedDef
                    context'
                    name
                    (Domain.Glued (Domain.Var fakeVar) mempty $ Lazy $ throwError $ Error.TypeMismatch mempty)
                    source
              domain <-
                Evaluation.evaluateClosure
                  domainClosure
                  (Domain.var v)
              source'' <-
                Readback.readback
                  (Context.toEnvironment context')
                  source
              body <- go alloweds' context'' domain
              pure $ Syntax.Lam (Binding.Unspanned name) source'' plicity body

            _ -> panic "pruneMeta wrong type"
