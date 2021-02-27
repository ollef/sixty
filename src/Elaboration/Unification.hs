{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
module Elaboration.Unification where

import Protolude hiding (catch, check, evaluate, force, head, throwIO)

import Control.Exception.Lifted
import Rock

import {-# source #-} qualified Elaboration
import qualified Builtin
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Elaboration.Meta as Meta
import qualified Core.Readback as Readback
import qualified Core.Syntax as Syntax
import Data.IntSeq (IntSeq)
import qualified Data.IntSeq as IntSeq
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Tsil as Tsil
import Data.Tsil (Tsil)
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import Environment (Environment(Environment))
import qualified Environment
import qualified Error
import Extra
import Flexibility (Flexibility)
import qualified Flexibility
import GHC.Exts (fromList)
import Index
import qualified Index.Map as Index
import Literal (Literal)
import qualified Meta
import Monad
import qualified Name
import Plicity
import qualified Query
import Telescope (Telescope)
import qualified Telescope
import Var

tryUnify :: Context v -> Domain.Value -> Domain.Value -> M (Syntax.Term v -> Syntax.Term v)
tryUnify context value1 value2 = do
  success <- Context.try_ context $ unify context Flexibility.Rigid value1 value2
  if success then
    pure identity
  else do
    type_ <- Readback.readback (Context.toEnvironment context) value2
    pure $ const $ Builtin.fail type_

tryUnifyD :: Context v -> Domain.Value -> Domain.Value -> M (Domain.Value -> Domain.Value)
tryUnifyD context value1 value2 = do
  success <- Context.try_ context $ unify context Flexibility.Rigid value1 value2
  pure $ if success then
    identity
  else
    const $ Builtin.Fail value2

unify :: Context v -> Flexibility -> Domain.Value -> Domain.Value -> M ()
unify context flexibility value1 value2 = do
  value1' <- Context.forceHeadGlue context value1
  value2' <- Context.forceHeadGlue context value2
  catchAndAdd $ case (value1', value2') of
    -- Both metas
    (Domain.Neutral (Domain.Meta metaIndex1) (Domain.Apps args1), Domain.Neutral (Domain.Meta metaIndex2) (Domain.Apps args2))
      | Flexibility.Rigid <- flexibility -> do
        args1' <- mapM (mapM $ Context.forceHead context) args1
        args2' <- mapM (mapM $ Context.forceHead context) args2
        if metaIndex1 == metaIndex2 && map fst args1 == map fst args2 then do
          -- Intersection: If the same metavar is applied to two different lists of unknown
          -- variables its solution must not mention any variables at
          -- positions where the lists differ.
          let
            keep =
              Tsil.zipWith (shouldKeepMetaArgument `on` snd) args1' args2'
          if and keep then
            Tsil.zipWithM_ (unify context flexibility `on` snd) args1 args2

          else
            pruneMeta context metaIndex1 keep

        else do
          let
            maybeUniqueVars1 = do
              vars1 <- mapM (mapM Domain.singleVarView) args1'
              guard $ unique $ snd <$> vars1
              pure vars1

            maybeUniqueVars2 = do
              vars2 <- mapM (mapM Domain.singleVarView) args2'
              guard $ unique $ snd <$> vars2
              pure vars2

          case (maybeUniqueVars1, maybeUniqueVars2) of
            (Just vars1, Just vars2)
              | length vars1 > length vars2 ->
                solve context metaIndex1 vars1 value2

              | otherwise ->
                solve context metaIndex2 vars2 value1

            (Just vars1, _) ->
              solve context metaIndex1 vars1 value2

            (_, Just vars2) ->
              solve context metaIndex2 vars2 value1

            _ ->
              can'tUnify

    -- Same heads
    (Domain.Neutral head1 spine1, Domain.Neutral head2 spine2)
      | head1 == head2 -> do
        let
          flexibility' =
            max (Domain.headFlexibility head1) flexibility

        unifySpines context flexibility' spine1 spine2

    (Domain.Con con1 args1, Domain.Con con2 args2)
      | con1 == con2
      , map fst args1 == map fst args2 ->
        Tsil.zipWithM_ (unify context flexibility `on` snd) args1 args2

      | otherwise ->
        can'tUnify

    (Domain.Lit lit1, Domain.Lit lit2)
      | lit1 == lit2 ->
        pure ()

      | otherwise ->
        can'tUnify

    (Domain.Lam bindings1 type1 plicity1 closure1, Domain.Lam _ type2 plicity2 closure2)
      | plicity1 == plicity2 ->
        unifyAbstraction (Bindings.toName bindings1) type1 closure1 type2 closure2

    (Domain.Pi binding1 domain1 plicity1 targetClosure1, Domain.Pi _ domain2 plicity2 targetClosure2)
      | plicity1 == plicity2 ->
        unifyAbstraction (Binding.toName binding1) domain1 targetClosure1 domain2 targetClosure2

    (Domain.Pi binding1 domain1 plicity1 targetClosure1, Domain.Fun domain2 plicity2 target2)
      | plicity1 == plicity2 -> do
        unify context flexibility domain2 domain1
        (context', var) <- Context.extend context (Binding.toName binding1) domain1
        target1 <- Evaluation.evaluateClosure targetClosure1 $ Domain.var var
        unify context' flexibility target1 target2

    (Domain.Fun domain1 plicity1 target1, Domain.Pi binding2 domain2 plicity2 targetClosure2)
      | plicity1 == plicity2 -> do
        unify context flexibility domain2 domain1
        (context', var) <- Context.extend context (Binding.toName binding2) domain2
        target2 <- Evaluation.evaluateClosure targetClosure2 $ Domain.var var
        unify context' flexibility target1 target2

    (Domain.Fun domain1 plicity1 target1, Domain.Fun domain2 plicity2 target2)
      | plicity1 == plicity2 -> do
        unify context flexibility domain2 domain1
        unify context flexibility target1 target2

    -- Eta expand
    (Domain.Lam bindings1 type1 plicity1 closure1, v2) -> do
      (context', var) <- Context.extend context (Bindings.toName bindings1) type1
      let
        varValue =
          Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 varValue
      body2 <- Evaluation.apply v2 plicity1 varValue

      unify context' flexibility body1 body2

    (v1, Domain.Lam bindings2 type2 plicity2 closure2) -> do
      (context', var) <- Context.extend context (Bindings.toName bindings2) type2
      let
        varValue =
          Domain.var var

      body1 <- Evaluation.apply v1 plicity2 varValue
      body2 <- Evaluation.evaluateClosure closure2 varValue

      unify context' flexibility body1 body2

    -- Glued values
    (Domain.Glued head1 spine1 value1'', Domain.Glued head2 spine2 value2'')
      | head1 == head2 ->
        unifySpines context Flexibility.Flexible spine1 spine2 `catch` \(_ :: Error.Elaboration) ->
          unifyForce flexibility value1'' value2''

    (Domain.Glued _ _ value1'', _) -> do
      value1''' <- force value1''
      unify context flexibility value1''' value2'

    (_, Domain.Glued _ _ value2'') -> do
      value2''' <- force value2''
      unify context flexibility value1' value2'''

    -- Metas
    (Domain.Neutral (Domain.Meta metaIndex1) (Domain.Apps args1), v2)
      | Flexibility.Rigid <- flexibility -> do
        args1' <- mapM (mapM $ Context.forceHead context) args1
        case traverse (traverse Domain.singleVarView) args1' of
          Just vars1
            | unique $ snd <$> vars1 ->
              solve context metaIndex1 vars1 v2

          _ ->
            can'tUnify

    (v1, Domain.Neutral (Domain.Meta metaIndex2) (Domain.Apps args2))
      | Flexibility.Rigid <- flexibility -> do
        args2' <- mapM (mapM $ Context.forceHead context) args2
        case traverse (traverse Domain.singleVarView) args2' of
          Just vars2
            | unique $ snd <$> vars2 ->
              solve context metaIndex2 vars2 v1

          _ ->
            can'tUnify

    -- Case inversion
    (Domain.Neutral (Domain.Meta meta) (spine@(Domain.Apps args) Domain.:> Domain.Case branches), _)
      | Flexibility.Rigid <- flexibility -> do
        matches <- potentiallyMatchingBranches context value2' branches
        invertCase meta spine args matches

    (_, Domain.Neutral (Domain.Meta meta) (spine@(Domain.Apps args) Domain.:> Domain.Case branches))
      | Flexibility.Rigid <- flexibility -> do
        matches <- potentiallyMatchingBranches context value1' branches
        invertCase meta spine args matches

    -- Failure terms mean that there has been an earlier error that's already
    -- been reported, so let's not trigger more errors from them.
    (Domain.Neutral (Domain.Global Builtin.FailName) _, _) ->
      pure ()

    (_, Domain.Neutral (Domain.Global Builtin.FailName) _) ->
      pure ()

    _ ->
      can'tUnify

  where
    unifyForce flexibility' lazyValue1 lazyValue2 = do
      v1 <- force lazyValue1
      v2 <- force lazyValue2
      unify context flexibility' v1 v2

    unifyAbstraction name type1 closure1 type2 closure2 = do
      unify context flexibility type1 type2

      (context', var) <- Context.extend context name type1
      let
        varValue =
          Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 varValue
      body2 <- Evaluation.evaluateClosure closure2 varValue
      unify context' flexibility body1 body2

    invertCase meta spine args matches =
      case matches of
        [Just (Left constr)] -> do
          metaType <- instantiatedMetaType context meta args
          appliedConstr <- fullyApplyToMetas context constr metaType
          unify context flexibility (Domain.Neutral (Domain.Meta meta) spine) appliedConstr
          unify context flexibility value1 value2

        [Just (Right lit)] -> do
          unify context flexibility (Domain.Neutral (Domain.Meta meta) spine) $ Domain.Lit lit
          unify context flexibility value1 value2

        _ ->
          can'tUnify

    catchAndAdd m =
      case flexibility of
        Flexibility.Rigid ->
          m `catch` \err ->
            case err of
              Error.TypeMismatch stack -> do
                term1 <- Elaboration.readback context value1
                term2 <- Elaboration.readback context value2
                pterm1 <- Context.toPrettyableTerm context term1
                pterm2 <- Context.toPrettyableTerm context term2
                throwIO $
                  Error.TypeMismatch $
                      stack Tsil.:>
                      ( pterm1
                      , pterm2
                      )

              Error.OccursCheck stack -> do
                term1 <- Elaboration.readback context value1
                term2 <- Elaboration.readback context value2
                pterm1 <- Context.toPrettyableTerm context term1
                pterm2 <- Context.toPrettyableTerm context term2
                throwIO $
                  Error.OccursCheck $
                      stack Tsil.:>
                      ( pterm1
                      , pterm2
                      )

              _ ->
                throwIO err

        Flexibility.Flexible ->
          m

    can'tUnify =
      throwIO $ Error.TypeMismatch mempty

unifySpines :: Context v -> Flexibility -> Domain.Spine -> Domain.Spine -> M ()
unifySpines context flexibility spine1 spine2 =
  case (spine1, spine2) of
    (Domain.Empty, Domain.Empty) ->
      pure ()

    (spine1' Domain.:> elimination1, spine2' Domain.:> elimination2) -> do
      unifySpines context flexibility spine1' spine2'
      case (elimination1, elimination2) of
        (Domain.App plicity1 arg1, Domain.App plicity2 arg2)
          | plicity1 == plicity2 ->
            unify context flexibility arg1 arg2

        (Domain.Case branches1, Domain.Case branches2) ->
          unifyBranches context flexibility branches1 branches2

        _ ->
          throwIO $ Error.TypeMismatch mempty

    _ ->
      throwIO $ Error.TypeMismatch mempty

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
  (Domain.Branches outerEnv2 branches2 defaultBranch2) =
    case (branches1, branches2) of
      (Syntax.ConstructorBranches conTypeName1 conBranches1, Syntax.ConstructorBranches conTypeName2 conBranches2)
        | conTypeName1 == conTypeName2 ->
          unifyMaps conBranches1 conBranches2 $ unifyTele outerContext outerEnv1 outerEnv2

      (Syntax.LiteralBranches litBranches1, Syntax.LiteralBranches litBranches2) ->
        unifyMaps litBranches1 litBranches2 unifyTerms

      _ ->
        can'tUnify

  where
    unifyMaps
      :: (Eq k, Hashable k)
      => OrderedHashMap k (x, v1)
      -> OrderedHashMap k (x, v2)
      -> (v1 -> v2 -> M ())
      -> M ()
    unifyMaps brs1 brs2 k = do
      let
        branches =
          OrderedHashMap.intersectionWith (,) brs1 brs2

        missing1 =
          OrderedHashMap.difference brs1 branches

        missing2 =
          OrderedHashMap.difference brs2 branches
      unless (OrderedHashMap.null missing1 && OrderedHashMap.null missing2)
        can'tUnify

      forM_ branches $ \((_, tele1), (_, tele2)) ->
        k tele1 tele2

      case (defaultBranch1, defaultBranch2) of
        (Just branch1, Just branch2) ->
          unifyTerms branch1 branch2

        (Nothing, Nothing) ->
          pure ()

        _ ->
          can'tUnify

    unifyTerms term1 term2 = do
      term1' <- Evaluation.evaluate outerEnv1 term1
      term2' <- Evaluation.evaluate outerEnv2 term2
      unify outerContext flexibility term1' term2'

    unifyTele
      :: Context v
      -> Domain.Environment v1
      -> Domain.Environment v2
      -> Telescope Bindings Syntax.Type Syntax.Term v1
      -> Telescope Bindings Syntax.Type Syntax.Term v2
      -> M ()
    unifyTele context env1 env2 tele1 tele2 =
      case (tele1, tele2) of
        (Telescope.Extend bindings1 type1 plicity1 tele1', Telescope.Extend _bindings2 type2 plicity2 tele2')
          | plicity1 == plicity2 -> do
            type1' <- Evaluation.evaluate env1 type1
            type2' <- Evaluation.evaluate env2 type2
            unify context flexibility type1' type2'
            (context', var) <- Context.extend context (Bindings.toName bindings1) type1'
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
      throwIO $ Error.TypeMismatch mempty

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
  -> M [Maybe (Either Name.QualifiedConstructor Literal)]
potentiallyMatchingBranches outerContext resultValue (Domain.Branches outerEnv branches defaultBranch) = do
  resultValue' <- Context.forceHead outerContext resultValue
  defaultBranch' <- fmap (catMaybes . toList) $ forM defaultBranch $ \branch -> do
    isMatch <- branchMatches outerContext resultValue' outerEnv $ Telescope.Empty branch
    pure $
      if isMatch then
        Just Nothing

      else
        Nothing

  branches' <- fmap catMaybes $
    case branches of
      Syntax.ConstructorBranches constructorTypeName constructorBranches ->
        forM (OrderedHashMap.toList constructorBranches) $ \(constr, (_, tele)) -> do
          isMatch <- branchMatches outerContext resultValue' outerEnv tele
          pure $
            if isMatch then
              Just $ Just $ Left $ Name.QualifiedConstructor constructorTypeName constr

            else
              Nothing

      Syntax.LiteralBranches literalBranches ->
        forM (OrderedHashMap.toList literalBranches) $ \(int, (_, branch)) -> do
          isMatch <- branchMatches outerContext resultValue' outerEnv $ Telescope.Empty branch
          pure $
            if isMatch then
              Just $ Just $ Right int

            else
              Nothing

  pure $ defaultBranch' <> branches'
  where
    branchMatches
      :: Context v
      -> Domain.Value
      -> Domain.Environment v'
      -> Telescope Bindings Syntax.Type Syntax.Term v'
      -> M Bool
    branchMatches context resultValue' env tele =
      case tele of
        Telescope.Empty body -> do
          body' <- Evaluation.evaluate env body
          body'' <- Context.forceHead context body'
          case (body'', resultValue') of
            (Domain.Neutral (Domain.Meta _) (Domain.Apps _), _) ->
              pure True

            (Domain.Neutral _ (_ Domain.:> Domain.Case branches'), _) -> do
              matches <- potentiallyMatchingBranches context resultValue branches'
              pure $ not $ null matches

            (Domain.Neutral head1 (Domain.Apps _), Domain.Neutral head2 (Domain.Apps _)) ->
              pure $ head1 == head2

            (Domain.Con con1 _, Domain.Con con2 _) ->
              pure $ con1 == con2

            (Domain.Lit l1, Domain.Lit l2) ->
              pure $ l1 == l2

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

            _ ->
              pure False

        Telescope.Extend bindings type_ _ tele' -> do
          type' <- Evaluation.evaluate env type_
          (context', var) <- Context.extend context (Bindings.toName bindings) type'
          branchMatches context' resultValue' (Environment.extendVar env var) tele'

instantiatedMetaType
  :: Context v
  -> Meta.Index
  -> Tsil (Plicity, Domain.Value)
  -> M Domain.Type
instantiatedMetaType context meta args = do
  solution <- Context.lookupMeta context meta
  case solution of
    Meta.Unsolved _ metaType _ _ _ -> do
      metaType' <-
        Evaluation.evaluate
          (Environment.empty $ Context.scopeKey context)
          metaType

      Context.instantiateType context metaType' $ toList args

    Meta.Solved {} ->
      panic "instantiatedMetaType already solved"

    Meta.LazilySolved {} ->
      panic "instantiatedMetaType already solved"

fullyApplyToMetas
  :: Context v
  -> Name.QualifiedConstructor
  -> Domain.Type
  -> M Domain.Value
fullyApplyToMetas context constr type_ = do
  type' <- Context.forceHead context type_
  case type' of
    Domain.Neutral (Domain.Global _typeName) (Domain.Apps typeArgs) -> do
      constrType <- fetch $ Query.ConstructorType constr
      constrType' <-
        Evaluation.evaluate
          (Environment.empty $ Context.scopeKey context)
          (Syntax.fromVoid $ Telescope.fold Syntax.Pi constrType)
      instantiatedConstrType <- Context.instantiateType context constrType' $ toList typeArgs
      (metas, _) <- Elaboration.insertMetas context Elaboration.UntilTheEnd instantiatedConstrType
      pure $ Domain.Con constr $ typeArgs <> fromList metas

    _ ->
      panic "fullyApplyToMetas"

-------------------------------------------------------------------------------

shouldKeepMetaArgument :: Domain.Value -> Domain.Value -> Bool
shouldKeepMetaArgument value1 value2 =
  case (value1, value2) of
    (Domain.Neutral (Domain.Var var1) Domain.Empty, Domain.Neutral (Domain.Var var2) Domain.Empty) ->
      var1 == var2

    (Domain.Neutral (Domain.Var _) Domain.Empty, _) ->
      not $ simpleNonVar value2

    (_, Domain.Neutral (Domain.Var _) Domain.Empty) ->
      not $ simpleNonVar value1

    _ ->
      True
  where
    simpleNonVar value =
      case value of
        Domain.Con _ Tsil.Empty ->
          True

        Domain.Neutral hd Domain.Empty ->
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
solve :: Context v -> Meta.Index -> Tsil (Plicity, Var) -> Domain.Value -> M ()
solve context meta vars value = do
  term <- checkSolution context meta vars value
  Context.solveMeta context meta term

-- | Occurs check, scope check, prune, and read back the solution at the same
-- time.
checkSolution
  :: Context v
  -> Meta.Index
  -> Tsil (Plicity, Var)
  -> Domain.Value
  -> M (Syntax.Term Void)
checkSolution outerContext meta vars value = do
  let
    indices =
      IntSeq.fromTsil $ snd <$> vars
  solution <-
    checkValueSolution
      outerContext
      meta
      Environment
        { scopeKey = Context.scopeKey outerContext
        , indices = Index.Map indices
        , values = Context.values outerContext
        , glueableBefore = Index $ IntSeq.size indices
        }
      Flexibility.Rigid
      value
  addAndCheckLambdas outerContext meta (fst <$> vars) indices solution

addAndCheckLambdas
  :: Context v
  -> Meta.Index
  -> Tsil Plicity
  -> IntSeq Var
  -> Syntax.Term v'
  -> M (Syntax.Term v')
addAndCheckLambdas outerContext meta plicities vars term =
  case (plicities, vars) of
    (Tsil.Empty, IntSeq.Empty) ->
      pure term

    (plicities' Tsil.:> plicity, vars' IntSeq.:> var) -> do
      let
        name =
          Context.lookupVarName var outerContext
        type_ =
          Context.lookupVarType var outerContext

      type' <-
        checkValueSolution
          outerContext
          meta
          Environment
            { scopeKey = Context.scopeKey outerContext
            , indices = Index.Map vars'
            , values = Context.values outerContext
            , glueableBefore = Index $ IntSeq.size vars'
            }
          Flexibility.Rigid
          type_
      let
        term' =
          Syntax.Lam (Bindings.Unspanned name) type' plicity (Syntax.succ term)
      addAndCheckLambdas outerContext meta plicities' vars' term'

    _ ->
      panic "addAndCheckLambdas length mismatch"

checkValueSolution
  :: Context v
  -> Meta.Index
  -> Domain.Environment v'
  -> Flexibility
  -> Domain.Value
  -> M (Syntax.Term v')
checkValueSolution outerContext occurs env flexibility value = do
  value' <- Context.forceHeadGlue outerContext value
  case value' of
    Domain.Neutral (Domain.Var var) spine ->
      case Environment.lookupVarIndex var env of
        Nothing ->
          throwIO $ Error.TypeMismatch mempty

        Just i ->
          checkSpineSolution outerContext occurs env flexibility (Syntax.Var i) spine

    Domain.Neutral (Domain.Global global) spine ->
      checkSpineSolution outerContext occurs env flexibility (Syntax.Global global) spine

    Domain.Neutral (Domain.Meta meta) spine -> do
      metaWeight <- Meta.entryWeight <$> Context.lookupMeta outerContext meta
      occursWeight <- Meta.entryWeight <$> Context.lookupMeta outerContext occurs
      case compare occursWeight metaWeight of
        LT ->
          Context.moveMetaBefore outerContext occurs meta

        EQ ->
          throwIO $ Error.OccursCheck mempty

        GT ->
          pure ()
      case spine of
        Domain.Apps args -> do
          args' <- mapM (Context.forceHead outerContext . snd) args
          case traverse Domain.singleVarView args' of
            Just vars
              | allowedVars <- map (\v -> isJust (Environment.lookupVarIndex v env) && isNothing (Environment.lookupVarValue v env)) vars
              , any not allowedVars
              -> do
                pruneMeta outerContext meta allowedVars
                checkValueSolution outerContext occurs env flexibility $ Domain.Neutral (Domain.Meta meta) spine

            _ ->
              checkSpineSolution outerContext occurs env flexibility (Syntax.Meta meta) spine

        _ ->
          checkSpineSolution outerContext occurs env flexibility (Syntax.Meta meta) spine

    Domain.Con con args ->
      Syntax.apps (Syntax.Con con) <$> mapM (mapM $ checkValueSolution outerContext occurs env flexibility) args

    Domain.Lit lit ->
      pure $ Syntax.Lit lit

    Domain.Glued (Domain.Global global) spine value'' ->
      checkSpineSolution outerContext occurs env Flexibility.Flexible (Syntax.Global global) spine `catch` \(_ :: Error.Elaboration) -> do
        value''' <- force value''
        checkValueSolution outerContext occurs env flexibility value'''

    Domain.Glued (Domain.Meta meta) spine value'' -> do
      occursWeight <- Meta.entryWeight <$> Context.lookupMeta outerContext occurs
      metaWeight <- Meta.entryWeight <$> Context.lookupMeta outerContext meta
      if metaWeight < occursWeight then
        -- The solved meta (`meta`) does not have the meta we're solving
        -- (`occurs`) in scope, so we can try without unfolding `meta`.
        checkSpineSolution outerContext occurs env Flexibility.Flexible (Syntax.Meta meta) spine `catch` \(_ :: Error.Elaboration) -> do
          value''' <- force value''
          checkValueSolution outerContext occurs env flexibility value'''
      else do
        -- The meta solution might contain `occurs`, so we need to force.
        value''' <- force value''
        checkValueSolution outerContext occurs env flexibility value'''

    Domain.Glued (Domain.Var _) _ value'' -> do
      -- The variable's value might contain `occurs`, so we need to force
      value''' <- force value''
      checkValueSolution outerContext occurs env flexibility value'''

    Domain.Lam bindings type_ plicity closure ->
      Syntax.Lam bindings
        <$> checkValueSolution outerContext occurs env flexibility type_
        <*> pure plicity
        <*> checkClosureSolution outerContext occurs env flexibility closure

    Domain.Pi binding type_ plicity closure ->
      Syntax.Pi binding
        <$> checkValueSolution outerContext occurs env flexibility type_
        <*> pure plicity
        <*> checkClosureSolution outerContext occurs env flexibility closure

    Domain.Fun domain plicity target ->
      Syntax.Fun
        <$> checkValueSolution outerContext occurs env flexibility domain
        <*> pure plicity
        <*> checkValueSolution outerContext occurs env flexibility target

checkBranchSolution
  :: Context outer
  -> Meta.Index
  -> Domain.Environment v
  -> Domain.Environment v'
  -> Flexibility
  -> Telescope Bindings Syntax.Type Syntax.Term v'
  -> M (Telescope Bindings Syntax.Type Syntax.Term v)
checkBranchSolution outerContext occurs outerEnv innerEnv flexibility tele =
  case tele of
    Telescope.Empty term -> do
      value <- Evaluation.evaluate innerEnv term
      term' <- checkValueSolution outerContext occurs outerEnv flexibility value
      pure $ Telescope.Empty term'

    Telescope.Extend bindings domain plicity tele' -> do
      domain' <- Evaluation.evaluate innerEnv domain
      domain'' <- checkValueSolution outerContext occurs outerEnv flexibility domain'
      (outerEnv', var) <- Environment.extend outerEnv
      let
        innerEnv' =
          Environment.extendVar innerEnv var
      tele'' <- checkBranchSolution outerContext occurs outerEnv' innerEnv' flexibility tele'
      pure $ Telescope.Extend bindings domain'' plicity tele''

checkClosureSolution
  :: Context v
  -> Meta.Index
  -> Domain.Environment v'
  -> Flexibility
  -> Domain.Closure
  -> M (Scope Syntax.Term v')
checkClosureSolution outerContext occurs env flexibility closure = do
  (env', v) <- Environment.extend env
  closure' <- Evaluation.evaluateClosure closure $ Domain.var v
  checkValueSolution outerContext occurs env' flexibility closure'

checkSpineSolution
  :: Context v
  -> Meta.Index
  -> Domain.Environment v'
  -> Flexibility
  -> Syntax.Term v'
  -> Domain.Spine
  -> M (Syntax.Term v')
checkSpineSolution outerContext occurs env flexibility head spine =
  case spine of
    Domain.Empty ->
      pure head

    spine' Domain.:> elim -> do
      inner <- checkSpineSolution outerContext occurs env flexibility head spine'
      checkEliminationSolution outerContext occurs env flexibility inner elim

checkEliminationSolution
  :: Context v
  -> Meta.Index
  -> Domain.Environment v'
  -> Flexibility
  -> Syntax.Term v'
  -> Domain.Elimination
  -> M (Syntax.Term v')
checkEliminationSolution outerContext occurs env flexibility eliminee elimination =
  case elimination of
    Domain.App plicity arg ->
      Syntax.App eliminee plicity <$>
        checkValueSolution outerContext occurs env flexibility arg

    Domain.Case (Domain.Branches env' branches defaultBranch) -> do
      branches' <- case branches of
        Syntax.ConstructorBranches constructorTypeName constructorBranches ->
          fmap (Syntax.ConstructorBranches constructorTypeName) $
            OrderedHashMap.forMUnordered constructorBranches $ mapM $
              checkBranchSolution outerContext occurs env env' flexibility

        Syntax.LiteralBranches literalBranches ->
          fmap Syntax.LiteralBranches $
            OrderedHashMap.forMUnordered literalBranches $ mapM $ \branch -> do
              branch' <- Evaluation.evaluate env' branch
              checkValueSolution outerContext occurs env flexibility branch'

      defaultBranch' <- forM defaultBranch $ \branch -> do
        branch' <- Evaluation.evaluate env' branch
        checkValueSolution outerContext occurs env flexibility branch'
      pure $ Syntax.Case eliminee branches' defaultBranch'

pruneMeta
  :: Context v
  -> Meta.Index
  -> Tsil Bool
  -> M ()
pruneMeta context meta allowedArgs = do
  entry <- Context.lookupMeta context meta
  -- putText $ "pruneMeta " <> show meta
  -- putText $ "pruneMeta " <> show allowedArgs
  case entry of
    Meta.Unsolved _ metaType _ _ _ -> do
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

    Meta.LazilySolved {} ->
      panic "pruneMeta already solved"

  where
    go :: [Bool] -> Context v -> Domain.Type -> M (Syntax.Term v)
    go alloweds context' type_ =
      case alloweds of
        [] -> do
          (meta', _, v) <- Context.newMetaReturningIndex context' type_
          Context.moveMetaBefore context meta meta'
          checkValueSolution context' meta (Context.toEnvironment context') Flexibility.Rigid v

        allowed:alloweds' -> do
          type' <- Context.forceHead context type_
          case type' of
            Domain.Fun domain plicity target -> do
              domain' <- checkValueSolution context' meta (Context.toEnvironment context') Flexibility.Rigid domain
              (context'', _) <-
                if allowed then
                  Context.extend context' "x" domain
                else do
                  fakeVar <- freshVar
                  typeMismatch <- lazy $ throwIO $ Error.TypeMismatch mempty
                  Context.extendDef
                    context'
                    "x"
                    (Domain.Glued (Domain.Var fakeVar) mempty typeMismatch)
                    domain
              body <- go alloweds' context'' target
              pure $ Syntax.Lam "x" domain' plicity body

            Domain.Pi binding domain plicity targetClosure -> do
              let
                name =
                  Binding.toName binding
              (context'', v) <-
                if allowed then
                  Context.extend context' name domain
                else do
                  fakeVar <- freshVar
                  typeMismatch <- lazy $ throwIO $ Error.TypeMismatch mempty
                  Context.extendDef
                    context'
                    name
                    (Domain.Glued (Domain.Var fakeVar) mempty typeMismatch)
                    domain
              target <-
                Evaluation.evaluateClosure
                  targetClosure
                  (Domain.var v)
              domain' <- checkValueSolution context' meta (Context.toEnvironment context') Flexibility.Rigid domain
              body <- go alloweds' context'' target
              pure $ Syntax.Lam (Bindings.Unspanned name) domain' plicity body

            _ -> panic "pruneMeta wrong type"
