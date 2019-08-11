{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module Unification.Indices where

import Protolude hiding (force, IntSet)

import Context (Context)
import qualified Context
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Tsil as Tsil
import qualified Domain
import Flexibility (Flexibility)
import qualified Flexibility
import Evaluation
import Index
import qualified Index.Map
import Monad
import Plicity
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

    (Domain.Pi name1 source1 plicity1 domainClosure1, Domain.Pi _ source2 plicity2 domainClosure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 source1 domainClosure1 source2 domainClosure2

    (Domain.Pi name1 source1 Explicit domainClosure1, Domain.Fun source2 domain2) -> do
      context1 <- unifyForce context flexibility source2 source1

      (context2, var) <- lift $ Context.extendUnnamed context1 name1 source1
      let
        lazyVar = Lazy $ pure $ Domain.var var

      domain1 <- lift $ Evaluation.evaluateClosure domainClosure1 lazyVar
      domain2' <- lift $ force domain2
      context3 <- unify context2 flexibility (IntSet.insert var untouchables) domain1 domain2'
      pure $ unextend context3

    (Domain.Fun source1 domain1, Domain.Pi name2 source2 Explicit domainClosure2) -> do
      context1 <- unifyForce context flexibility source2 source1

      (context2, var) <- lift $ Context.extendUnnamed context1 name2 source2
      let
        lazyVar = Lazy $ pure $ Domain.var var

      domain1' <- lift $ force domain1
      domain2 <- lift $ Evaluation.evaluateClosure domainClosure2 lazyVar
      context3 <- unify context2 flexibility (IntSet.insert var untouchables) domain1' domain2
      pure $ unextend context3

    (Domain.Fun source1 domain1, Domain.Fun source2 domain2) -> do
      context1 <- unifyForce context flexibility source2 source1
      unifyForce context1 flexibility domain1 domain2

    -- Eta expand
    (Domain.Lam name1 type1 plicity1 closure1, v2) -> do
      (context1, var) <- lift $ Context.extendUnnamed context name1 type1
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- lift $ Evaluation.evaluateClosure closure1 lazyVar
      body2 <- lift $ Evaluation.apply v2 plicity1 lazyVar

      context2 <- unify context1 flexibility (IntSet.insert var untouchables) body1 body2
      pure $ unextend context2

    (v1, Domain.Lam name2 type2 plicity2 closure2) -> do
      (context1, var) <- lift $ Context.extendUnnamed context name2 type2
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- lift $ Evaluation.apply v1 plicity2 lazyVar
      body2 <- lift $ Evaluation.evaluateClosure closure2 lazyVar

      context2 <- unify context1 flexibility (IntSet.insert var untouchables) body1 body2
      pure $ unextend context2

    -- Vars
    (Domain.Neutral (Domain.Var var1) Tsil.Empty, _)
      | Flexibility.Rigid <- flexibility ->
        solve var1 value2'

    (_, Domain.Neutral (Domain.Var var2) Tsil.Empty)
      | Flexibility.Rigid <- flexibility ->
        solve var2 value1'

    _ ->
      throwError Dunno

  where
    unifyForce context' flexibility' lazyValue1 lazyValue2 = do
      v1 <- lift $ force lazyValue1
      v2 <- lift $ force lazyValue2
      unify context' flexibility' untouchables v1 v2

    unifySpines flexibility' spine1 spine2 =
      foldM
        (\context' -> uncurry (unifyForce context' flexibility' `on` snd))
        context
        (Tsil.zip spine1 spine2)

    unifyAbstraction name type1 closure1 type2 closure2 = do
      context1 <- unifyForce context flexibility type1 type2

      (context2, var) <- lift $ Context.extendUnnamed context1 name type1
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body1 <- lift $ Evaluation.evaluateClosure closure1 lazyVar
      body2 <- lift $ Evaluation.evaluateClosure closure2 lazyVar
      context3 <- unify context2 flexibility (IntSet.insert var untouchables) body1 body2
      pure $ unextend context3

    unextend :: Context (Succ v) -> Context v
    unextend context' =
      case Context.indices context' of
        indices Index.Map.:> _ ->
          context' { Context.indices = indices }

        _ ->
          panic "Unification.Indices.unify.unextend"

    solve var value
      | IntSet.member var untouchables =
        throwError Dunno

      | otherwise = do
        occurs context (IntSet.insert var untouchables) value
        pure $ Context.define context var $ Lazy $ pure value

occurs :: Context v -> IntSet Var -> Domain.Value -> E M ()
occurs context untouchables value = do
  value' <- lift $ Context.forceHead context value
  case value' of
    Domain.Neutral (Domain.Var var) _
      | IntSet.member var untouchables ->
        throwError Dunno

    Domain.Glued hd spine value'' ->
      occurs context untouchables (Domain.Neutral hd spine) `catchError` \_ ->
        occursForce value''

    Domain.Neutral _ spine ->
      mapM_ (occursForce . snd) spine

    Domain.Lam name type_ _ closure ->
      occursAbstraction name type_ closure

    Domain.Pi name source _ domainClosure ->
      occursAbstraction name source domainClosure

    Domain.Fun source domain -> do
      occursForce source
      occursForce domain

    Domain.Case _ _ ->
      -- TODO actually implement this
      throwError Dunno

  where
    occursForce lazyValue = do
      value' <- lift $ force lazyValue
      occurs context untouchables value'

    occursAbstraction name type_ closure = do
      occursForce type_
      (context', var) <- lift $ Context.extendUnnamed context name type_
      let
        lazyVar = Lazy $ pure $ Domain.var var

      body <- lift $ Evaluation.evaluateClosure closure lazyVar
      occurs context' untouchables body
