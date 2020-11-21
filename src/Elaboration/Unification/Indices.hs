{-# language DeriveAnyClass #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
module Elaboration.Unification.Indices where

import Protolude hiding (catch, force, IntSet, throwIO)

import Control.Exception.Lifted
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap

import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Syntax as Syntax
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Tsil as Tsil
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import qualified Environment
import Flexibility (Flexibility)
import qualified Flexibility
import Index
import qualified Index.Map
import Monad
import Telescope (Telescope)
import qualified Telescope
import Var

data Error
  = Nope
  | Dunno
  deriving (Eq, Ord, Show, Exception)

unify
  :: Int
  -> Context v
  -> Flexibility
  -> IntSet Var
  -> Domain.Value
  -> Domain.Value
  -> M (Context v)
unify glueFuel context flexibility untouchables value1 value2 = do
  value1' <- Context.forceHeadGlue context value1
  value2' <- Context.forceHeadGlue context value2
  case (value1', value2') of
    -- Same heads
    (Domain.Neutral head1 spine1, Domain.Neutral head2 spine2)
      | head1 == head2 -> do
        let
          flexibility' =
            max (Domain.headFlexibility head1) flexibility

        unifySpines glueFuel context flexibility' untouchables spine1 spine2

    (Domain.Con con1 args1, Domain.Con con2 args2)
      | con1 == con2
      , map fst args1 == map fst args2 ->
        foldM
          (\context' -> uncurry (unify glueFuel context' flexibility untouchables `on` snd))
          context
          (Tsil.zip args1 args2)

      | otherwise ->
        throwIO Nope

    (Domain.Lit lit1, Domain.Lit lit2)
      | lit1 == lit2 ->
        pure context

      | otherwise ->
        throwIO Nope

    (Domain.Glued head1 spine1 value1'', Domain.Glued head2 spine2 value2'')
      | glueFuel > 0
      , head1 == head2 ->
        unifySpines (glueFuel - 1) context Flexibility.Flexible untouchables spine1 spine2 `catch` \(_ :: Error) ->
          unifyForce (glueFuel - 1) context flexibility value1'' value2''

    (Domain.Glued head1 spine1 _, Domain.Glued head2 spine2 _)
      | glueFuel == 0
      , head1 == head2
      , Flexibility.Flexible <- flexibility ->
        unifySpines glueFuel context Flexibility.Flexible untouchables spine1 spine2

    (Domain.Glued _ _ value1'', _)
      | glueFuel > 0
      || flexibility == Flexibility.Rigid -> do
        value1''' <- force value1''
        unify glueFuel context flexibility untouchables value1''' value2'

    (_, Domain.Glued _ _ value2'')
      | glueFuel > 0
      || flexibility == Flexibility.Rigid -> do
        value2''' <- force value2''
        unify glueFuel context flexibility untouchables value1' value2'''

    (Domain.Lam bindings1 type1 plicity1 closure1, Domain.Lam _ type2 plicity2 closure2)
      | plicity1 == plicity2 ->
        unifyAbstraction (Bindings.toName bindings1) type1 closure1 type2 closure2

    (Domain.Pi binding1 domain1 plicity1 targetClosure1, Domain.Pi _ domain2 plicity2 targetClosure2)
      | plicity1 == plicity2 ->
        unifyAbstraction (Binding.toName binding1) domain1 targetClosure1 domain2 targetClosure2

    (Domain.Pi binding1 domain1 plicity1 targetClosure1, Domain.Fun domain2 plicity2 target2)
      | plicity1 == plicity2 -> do
        context1 <- unify glueFuel context flexibility untouchables domain2 domain1
        (context2, var) <- Context.extend context1 (Binding.toName binding1) domain1
        target1 <- Evaluation.evaluateClosure targetClosure1 $ Domain.var var
        context3 <- unify glueFuel context2 flexibility (IntSet.insert var untouchables) target1 target2
        pure $ unextend context3

    (Domain.Fun domain1 plicity1 target1, Domain.Pi binding2 domain2 plicity2 targetClosure2)
      | plicity1 == plicity2 -> do
        context1 <- unify glueFuel context flexibility untouchables domain2 domain1
        (context2, var) <- Context.extend context1 (Binding.toName binding2) domain2
        target2 <- Evaluation.evaluateClosure targetClosure2 $ Domain.var var
        context3 <- unify glueFuel context2 flexibility (IntSet.insert var untouchables) target1 target2
        pure $ unextend context3

    (Domain.Fun domain1 plicity1 target1, Domain.Fun domain2 plicity2 target2)
      | plicity1 == plicity2 -> do
        context1 <- unify glueFuel context flexibility untouchables domain2 domain1
        unify glueFuel context1 flexibility untouchables target1 target2

    -- Eta expand
    (Domain.Lam bindings1 type1 plicity1 closure1, v2) -> do
      (context1, var) <- Context.extend context (Bindings.toName bindings1) type1
      let
        varValue =
          Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 varValue
      body2 <- Evaluation.apply v2 plicity1 varValue

      context2 <- unify glueFuel context1 flexibility (IntSet.insert var untouchables) body1 body2
      pure $ unextend context2

    (v1, Domain.Lam bindings2 type2 plicity2 closure2) -> do
      (context1, var) <- Context.extend context (Bindings.toName bindings2) type2
      let
        varValue =
          Domain.var var

      body1 <- Evaluation.apply v1 plicity2 varValue
      body2 <- Evaluation.evaluateClosure closure2 varValue

      context2 <- unify glueFuel context1 flexibility (IntSet.insert var untouchables) body1 body2
      pure $ unextend context2

    -- Vars
    (Domain.Neutral (Domain.Var var1) Domain.Empty, _)
      | Flexibility.Rigid <- flexibility ->
        solve var1 value2'

    (_, Domain.Neutral (Domain.Var var2) Domain.Empty)
      | Flexibility.Rigid <- flexibility ->
        solve var2 value1'

    _ ->
      throwIO Dunno

  where
    unifyForce glueFuel' context' flexibility' lazyValue1 lazyValue2 = do
      v1 <- force lazyValue1
      v2 <- force lazyValue2
      unify glueFuel' context' flexibility' untouchables v1 v2

    unifyAbstraction name type1 closure1 type2 closure2 = do
      context1 <- unify glueFuel context flexibility untouchables type1 type2

      (context2, var) <- Context.extend context1 name type1
      let
        varValue =
          Domain.var var

      body1 <- Evaluation.evaluateClosure closure1 varValue
      body2 <- Evaluation.evaluateClosure closure2 varValue
      context3 <- unify glueFuel context2 flexibility (IntSet.insert var untouchables) body1 body2
      pure $ unextend context3

    solve var value
      | IntSet.member var untouchables =
        throwIO Dunno

      | otherwise = do
        occurs context Flexibility.Rigid (IntSet.insert var untouchables) value
        Context.define context var value

unifySpines
  :: Int
  -> Context v
  -> Flexibility
  -> IntSet Var
  -> Domain.Spine
  -> Domain.Spine
  -> M (Context v)
unifySpines glueFuel context flexibility untouchables spine1 spine2 =
  case (spine1, spine2) of
    (Domain.Empty, Domain.Empty) ->
      pure context

    (spine1' Domain.:> elimination1, spine2' Domain.:> elimination2) -> do
      context' <- unifySpines glueFuel context flexibility untouchables spine1' spine2'
      case (elimination1, elimination2) of
        (Domain.App plicity1 arg1, Domain.App plicity2 arg2)
          | plicity1 == plicity2 ->
            unify glueFuel context' flexibility untouchables arg1 arg2

        (Domain.Case branches1, Domain.Case branches2) ->
          unifyBranches glueFuel context' flexibility untouchables branches1 branches2

        _ ->
          throwIO Dunno

    _ ->
      throwIO Dunno

unifyBranches
  :: forall v
  . Int
  -> Context v
  -> Flexibility
  -> IntSet Var
  -> Domain.Branches
  -> Domain.Branches
  -> M (Context v)
unifyBranches
  glueFuel
  outerContext
  flexibility
  outerUntouchables
  (Domain.Branches outerEnv1 branches1 defaultBranch1)
  (Domain.Branches outerEnv2 branches2 defaultBranch2) =
    case (branches1, branches2) of
      (Syntax.ConstructorBranches conTypeName1 conBranches1, Syntax.ConstructorBranches conTypeName2 conBranches2)
        | conTypeName1 == conTypeName2 ->
          unifyMaps conBranches1 conBranches2 $ unifyTele outerEnv1 outerEnv2 outerUntouchables

      (Syntax.LiteralBranches litBranches1, Syntax.LiteralBranches litBranches2) ->
        unifyMaps litBranches1 litBranches2 unifyTerms

      _ ->
        throwIO Dunno
  where
    unifyMaps
      :: (Eq k, Hashable k)
      => OrderedHashMap k (x, v1)
      -> OrderedHashMap k (x, v2)
      -> (Context v -> v1 -> v2 -> M (Context v))
      -> M (Context v)
    unifyMaps brs1 brs2 k = do
      let
        branches =
          OrderedHashMap.intersectionWith (,) brs1 brs2

        missing1 =
          OrderedHashMap.difference brs1 branches

        missing2 =
          OrderedHashMap.difference brs2 branches
      unless (OrderedHashMap.null missing1 && OrderedHashMap.null missing2) $
        throwIO Dunno

      context' <-
        foldM
          (\context ((_, tele1), (_, tele2)) -> k context tele1 tele2)
          outerContext
          branches

      case (defaultBranch1, defaultBranch2) of
        (Just branch1, Just branch2) ->
          unifyTerms context' branch1 branch2

        (Nothing, Nothing) ->
          pure context'

        _ ->
          throwIO Dunno

    unifyTerms context term1 term2 = do
      term1' <- Evaluation.evaluate outerEnv1 term1
      term2' <- Evaluation.evaluate outerEnv2 term2
      unify glueFuel context flexibility outerUntouchables term1' term2'

    unifyTele
      :: Domain.Environment v1
      -> Domain.Environment v2
      -> IntSet Var
      -> Context v'
      -> Telescope Bindings Syntax.Type Syntax.Term v1
      -> Telescope Bindings Syntax.Type Syntax.Term v2
      -> M (Context v')
    unifyTele env1 env2 untouchables context tele1 tele2 =
      case (tele1, tele2) of
        (Telescope.Extend bindings1 type1 plicity1 tele1', Telescope.Extend _bindings2 type2 plicity2 tele2')
          | plicity1 == plicity2 -> do
            type1' <- Evaluation.evaluate env1 type1
            type2' <- Evaluation.evaluate env2 type2
            context' <- unify glueFuel context flexibility untouchables type1' type2'
            (context'', var) <- Context.extend context' (Bindings.toName bindings1) type1'
            context''' <-
              unifyTele
                (Environment.extendVar env1 var)
                (Environment.extendVar env2 var)
                (IntSet.insert var untouchables)
                context''
                tele1'
                tele2'
            pure $ unextend context'''

        (Telescope.Empty body1, Telescope.Empty body2) -> do
          body1' <- Evaluation.evaluate env1 body1
          body2' <- Evaluation.evaluate env2 body2
          unify glueFuel context flexibility untouchables body1' body2'

        _ ->
          panic "unifyTele"

unextend :: Context (Succ v) -> Context v
unextend context' =
  case Context.indices context' of
    indices Index.Map.:> _ ->
      context' { Context.indices = indices }

    _ ->
      panic "Unification.Indices.unextend"

occurs :: Context v -> Flexibility -> IntSet Var -> Domain.Value -> M ()
occurs context flexibility untouchables value = do
  value' <- Context.forceHeadGlue context value
  case value' of
    Domain.Neutral hd spine -> do
      occursHead flexibility untouchables hd
      Domain.mapM_ (occursElimination context (max (Domain.headFlexibility hd) flexibility) untouchables) spine

    Domain.Con _ args ->
      mapM_ (occurs context flexibility untouchables . snd) args

    Domain.Lit _ ->
      pure ()

    Domain.Glued (Domain.Var _) _ value'' ->
      occursForce value''

    Domain.Glued hd spine value'' ->
      occurs context Flexibility.Flexible untouchables (Domain.Neutral hd spine) `catch` \(_ :: Error) ->
        occursForce value''

    Domain.Lam bindings type_ _ closure ->
      occursAbstraction (Bindings.toName bindings) type_ closure

    Domain.Pi binding domain _ targetClosure ->
      occursAbstraction (Binding.toName binding) domain targetClosure

    Domain.Fun domain _ target -> do
      occurs context flexibility untouchables domain
      occurs context flexibility untouchables target

  where
    occursForce lazyValue = do
      value' <- force lazyValue
      occurs context flexibility untouchables value'

    occursAbstraction name type_ closure = do
      occurs context flexibility untouchables type_
      (context', var) <- Context.extend context name type_
      let
        varValue =
          Domain.var var

      body <- Evaluation.evaluateClosure closure varValue
      occurs context' flexibility untouchables body

occursHead
  :: Flexibility
  -> IntSet Var
  -> Domain.Head
  -> M ()
occursHead flexibility untouchables hd =
  case hd of
    Domain.Var var
      | IntSet.member var untouchables ->
        throwIO $
          case flexibility of
            Flexibility.Rigid ->
              Nope

            Flexibility.Flexible ->
              Dunno

      | otherwise ->
        pure ()

    Domain.Global _ ->
      pure ()

    Domain.Meta _ ->
      pure ()

occursElimination
  :: Context v
  -> Flexibility
  -> IntSet Var
  -> Domain.Elimination
  -> M ()
occursElimination context flexibility untouchables elimination =
  case elimination of
    Domain.App _plicity arg ->
      occurs context flexibility untouchables arg

    Domain.Case branches ->
      occursBranches context flexibility untouchables branches

occursBranches
  :: Context v
  -> Flexibility
  -> IntSet Var
  -> Domain.Branches
  -> M ()
occursBranches outerContext flexibility outerUntouchables (Domain.Branches outerEnv branches defaultBranch) = do
  case branches of
    Syntax.ConstructorBranches _ constructorBranches ->
      forM_ constructorBranches $ mapM_ $ occursTele outerContext outerUntouchables outerEnv

    Syntax.LiteralBranches literalBranches ->
      forM_ literalBranches $ mapM_ $ \branch ->
        occursTele outerContext outerUntouchables outerEnv $ Telescope.Empty branch
  forM_ defaultBranch $ \branch ->
    occursTele outerContext outerUntouchables outerEnv $ Telescope.Empty branch
  where
    occursTele
      :: Context v
      -> IntSet Var
      -> Domain.Environment v1
      -> Telescope Bindings Syntax.Type Syntax.Term v1
      -> M ()
    occursTele context untouchables env tele =
      case tele of
        Telescope.Extend bindings type_ _plicity tele' -> do
          type' <- Evaluation.evaluate env type_
          occurs context flexibility untouchables type'
          (context'', var) <- Context.extend context (Bindings.toName bindings) type'
          occursTele
            context''
            (IntSet.insert var untouchables)
            (Environment.extendVar env var)
            tele'
        Telescope.Empty body -> do
          body' <- Evaluation.evaluate env body
          occurs context flexibility untouchables body'
