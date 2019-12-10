{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
module Unification.Indices where

import Protolude hiding (force, IntSet)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import Context (Context)
import qualified Context
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Environment
import Evaluation
import Flexibility (Flexibility)
import qualified Flexibility
import Index
import qualified Index.Map
import Monad
import qualified Binding
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var

data Error
  = Nope
  | Dunno
  deriving (Eq, Ord, Show)

type E = ExceptT Error

unify
  :: Context v
  -> Flexibility
  -> IntSet Var
  -> Domain.Value
  -> Domain.Value
  -> E M (Context v)
unify context flexibility untouchables value1 value2 = do
  value1' <- lift $ Context.forceHeadGlue context value1
  value2' <- lift $ Context.forceHeadGlue context value2
  case (value1', value2') of
    -- Same heads
    (Domain.Neutral head1 spine1, Domain.Neutral head2 spine2)
      | head1 == head2 -> do
        let
          flexibility' =
            max (Domain.headFlexibility head1) flexibility

        unifySpines flexibility' spine1 spine2

    (Domain.Neutral (Domain.Con con1) _, Domain.Neutral (Domain.Con con2) _)
      | con1 /= con2 ->
        throwError Nope

    (Domain.Glued head1 spine1 value1'', Domain.Glued head2 spine2 value2'')
      | head1 == head2 ->
        unifySpines Flexibility.Flexible spine1 spine2 `catchError` \_ ->
          unifyForce context flexibility value1'' value2''

    (Domain.Glued _ _ value1'', _) -> do
      value1''' <- lift $ force value1''
      unify context flexibility untouchables value1''' value2'

    (_, Domain.Glued _ _ value2'') -> do
      value2''' <- lift $ force value2''
      unify context flexibility untouchables value1' value2'''

    (Domain.Lam name1 type1 plicity1 closure1, Domain.Lam _ type2 plicity2 closure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 type1 closure1 type2 closure2

    (Domain.Pi name1 domain1 plicity1 targetClosure1, Domain.Pi _ domain2 plicity2 targetClosure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 domain1 targetClosure1 domain2 targetClosure2

    (Domain.Pi name1 domain1 plicity1 targetClosure1, Domain.Fun domain2 plicity2 target2)
      | plicity1 == plicity2 -> do
        context1 <- unify context flexibility untouchables domain2 domain1
        (context2, var) <- lift $ Context.extendUnnamed context1 name1 domain1
        target1 <- lift $ Evaluation.evaluateClosure targetClosure1 $ Domain.var var
        context3 <- unify context2 flexibility (IntSet.insert var untouchables) target1 target2
        pure $ unextend context3

    (Domain.Fun domain1 plicity1 target1, Domain.Pi name2 domain2 plicity2 targetClosure2)
      | plicity1 == plicity2 -> do
        context1 <- unify context flexibility untouchables domain2 domain1
        (context2, var) <- lift $ Context.extendUnnamed context1 name2 domain2
        target2 <- lift $ Evaluation.evaluateClosure targetClosure2 $ Domain.var var
        context3 <- unify context2 flexibility (IntSet.insert var untouchables) target1 target2
        pure $ unextend context3

    (Domain.Fun domain1 plicity1 target1, Domain.Fun domain2 plicity2 target2)
      | plicity1 == plicity2 -> do
        context1 <- unify context flexibility untouchables domain2 domain1
        unify context1 flexibility untouchables target1 target2

    -- Eta expand
    (Domain.Lam name1 type1 plicity1 closure1, v2) -> do
      (context1, var) <- lift $ Context.extendUnnamed context name1 type1
      let
        varValue =
          Domain.var var

      body1 <- lift $ Evaluation.evaluateClosure closure1 varValue
      body2 <- lift $ Evaluation.apply v2 plicity1 varValue

      context2 <- unify context1 flexibility (IntSet.insert var untouchables) body1 body2
      pure $ unextend context2

    (v1, Domain.Lam name2 type2 plicity2 closure2) -> do
      (context1, var) <- lift $ Context.extendUnnamed context name2 type2
      let
        varValue =
          Domain.var var

      body1 <- lift $ Evaluation.apply v1 plicity2 varValue
      body2 <- lift $ Evaluation.evaluateClosure closure2 varValue

      context2 <- unify context1 flexibility (IntSet.insert var untouchables) body1 body2
      pure $ unextend context2

    -- Vars
    (Domain.Neutral (Domain.Var var1) Tsil.Empty, _)
      | Flexibility.Rigid <- flexibility ->
        solve var1 value2'

    (_, Domain.Neutral (Domain.Var var2) Tsil.Empty)
      | Flexibility.Rigid <- flexibility ->
        solve var2 value1'

    -- Case expressions
    (Domain.Case scrutinee1 branches1, Domain.Case scrutinee2 branches2) -> do
      context' <- unify context Flexibility.Flexible untouchables scrutinee1 scrutinee2
      unifyBranches context' flexibility untouchables branches1 branches2

    _ ->
      throwError Dunno

  where
    unifyForce context' flexibility' lazyValue1 lazyValue2 = do
      v1 <- lift $ force lazyValue1
      v2 <- lift $ force lazyValue2
      unify context' flexibility' untouchables v1 v2

    unifySpines flexibility' spine1 spine2 =
      foldM
        (\context' -> uncurry (unify context' flexibility' untouchables `on` snd))
        context
        (Tsil.zip spine1 spine2)

    unifyAbstraction name type1 closure1 type2 closure2 = do
      context1 <- unify context flexibility untouchables type1 type2

      (context2, var) <- lift $ Context.extendUnnamed context1 name type1
      let
        varValue =
          Domain.var var

      body1 <- lift $ Evaluation.evaluateClosure closure1 varValue
      body2 <- lift $ Evaluation.evaluateClosure closure2 varValue
      context3 <- unify context2 flexibility (IntSet.insert var untouchables) body1 body2
      pure $ unextend context3

    solve var value
      | IntSet.member var untouchables =
        throwError Dunno

      | otherwise = do
        occurs context Flexibility.Rigid (IntSet.insert var untouchables) value
        lift $ Context.define context var value

unifyBranches
  :: forall v
  . Context v
  -> Flexibility
  -> IntSet Var
  -> Domain.Branches
  -> Domain.Branches
  -> E M (Context v)
unifyBranches
  outerContext
  flexibility
  outerUntouchables
  (Domain.Branches outerEnv1 branches1 defaultBranch1)
  (Domain.Branches outerEnv2 branches2 defaultBranch2) =
    case (branches1, branches2) of
      (Syntax.ConstructorBranches conBranches1, Syntax.ConstructorBranches conBranches2) ->
        unifyMaps conBranches1 conBranches2 $ unifyTele outerEnv1 outerEnv2 outerUntouchables

      (Syntax.LiteralBranches litBranches1, Syntax.LiteralBranches litBranches2) ->
        unifyMaps litBranches1 litBranches2 unifyTerms

      _ ->
        throwError Dunno
  where
    unifyMaps
      :: (Eq k, Hashable k)
      => HashMap k (x, v1)
      -> HashMap k (x, v2)
      -> (Context v -> v1 -> v2 -> E M (Context v))
      -> E M (Context v)
    unifyMaps brs1 brs2 k = do
      let
        branches =
          HashMap.intersectionWith (,) brs1 brs2

        missing1 =
          HashMap.difference brs1 branches

        missing2 =
          HashMap.difference brs2 branches
      unless (HashMap.null missing1 && HashMap.null missing2) $
        throwError Dunno

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
          throwError Dunno

    unifyTerms context term1 term2 = do
      term1' <- lift $ Evaluation.evaluate outerEnv1 term1
      term2' <- lift $ Evaluation.evaluate outerEnv2 term2
      unify context flexibility outerUntouchables term1' term2'

    unifyTele
      :: Domain.Environment v1
      -> Domain.Environment v2
      -> IntSet Var
      -> Context v'
      -> Telescope Syntax.Type Syntax.Term v1
      -> Telescope Syntax.Type Syntax.Term v2
      -> E M (Context v')
    unifyTele env1 env2 untouchables context tele1 tele2 =
      case (tele1, tele2) of
        (Telescope.Extend binding1 type1 plicity1 tele1', Telescope.Extend _binding2 type2 plicity2 tele2')
          | plicity1 == plicity2 -> do
            type1' <- lift $ Evaluation.evaluate env1 type1
            type2' <- lift $ Evaluation.evaluate env2 type2
            context' <- unify context flexibility untouchables type1' type2'
            (context'', var) <- lift $ Context.extendUnnamed context' (Binding.toName binding1) type1'
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
          body1' <- lift $ Evaluation.evaluate env1 body1
          body2' <- lift $ Evaluation.evaluate env2 body2
          unify context flexibility untouchables body1' body2'

        _ ->
          panic "unifyTele"

unextend :: Context (Succ v) -> Context v
unextend context' =
  case Context.indices context' of
    indices Index.Map.:> _ ->
      context' { Context.indices = indices }

    _ ->
      panic "Unification.Indices.unextend"

occurs :: Context v -> Flexibility -> IntSet Var -> Domain.Value -> E M ()
occurs context flexibility untouchables value = do
  value' <- lift $ Context.forceHeadGlue context value
  case value' of
    Domain.Neutral (Domain.Var var) _
      | IntSet.member var untouchables ->
        throwError $
          case flexibility of
            Flexibility.Rigid ->
              Nope

            Flexibility.Flexible ->
              Dunno

    Domain.Int _ ->
      pure ()

    Domain.Glued (Domain.Var _) _ value'' ->
      occursForce value''

    Domain.Glued hd spine value'' ->
      occurs context Flexibility.Flexible untouchables (Domain.Neutral hd spine) `catchError` \_ ->
        occursForce value''

    Domain.Neutral hd spine ->
      mapM_ (occurs context (max (Domain.headFlexibility hd) flexibility) untouchables . snd) spine

    Domain.Lam name type_ _ closure ->
      occursAbstraction name type_ closure

    Domain.Pi name domain _ targetClosure ->
      occursAbstraction name domain targetClosure

    Domain.Fun domain _ target -> do
      occurs context flexibility untouchables domain
      occurs context flexibility untouchables target

    Domain.Case scrutinee branches -> do
      occurs context flexibility untouchables scrutinee
      occursBranches context flexibility untouchables branches

  where
    occursForce lazyValue = do
      value' <- lift $ force lazyValue
      occurs context flexibility untouchables value'

    occursAbstraction name type_ closure = do
      occurs context flexibility untouchables type_
      (context', var) <- lift $ Context.extendUnnamed context name type_
      let
        varValue =
          Domain.var var

      body <- lift $ Evaluation.evaluateClosure closure varValue
      occurs context' flexibility untouchables body

occursBranches
  :: Context v
  -> Flexibility
  -> IntSet Var
  -> Domain.Branches
  -> E M ()
occursBranches outerContext flexibility outerUntouchables (Domain.Branches outerEnv branches defaultBranch) = do
  case branches of
    Syntax.ConstructorBranches constructorBranches ->
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
      -> Telescope Syntax.Type Syntax.Term v1
      -> E M ()
    occursTele context untouchables env tele =
      case tele of
        Telescope.Extend binding type_ _plicity tele' -> do
          type' <- lift $ Evaluation.evaluate env type_
          occurs context flexibility untouchables type'
          (context'', var) <- lift $ Context.extendUnnamed context (Binding.toName binding) type'
          occursTele
            context''
            (IntSet.insert var untouchables)
            (Environment.extendVar env var)
            tele'
        Telescope.Empty body -> do
          body' <- lift $ Evaluation.evaluate env body
          occurs context flexibility untouchables body'
