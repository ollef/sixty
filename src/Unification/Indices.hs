{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module Unification.Indices where

import Protolude hiding (force, IntSet)

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
import Plicity
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

    (Domain.Pi name1 source1 plicity1 domainClosure1, Domain.Pi _ source2 plicity2 domainClosure2)
      | plicity1 == plicity2 ->
      unifyAbstraction name1 source1 domainClosure1 source2 domainClosure2

    (Domain.Pi name1 source1 Explicit domainClosure1, Domain.Fun source2 domain2) -> do
      context1 <- unify context flexibility untouchables source2 source1
      (context2, var) <- lift $ Context.extendUnnamed context1 name1 source1
      domain1 <- lift $ Evaluation.evaluateClosure domainClosure1 $ Domain.var var
      context3 <- unify context2 flexibility (IntSet.insert var untouchables) domain1 domain2
      pure $ unextend context3

    (Domain.Fun source1 domain1, Domain.Pi name2 source2 Explicit domainClosure2) -> do
      context1 <- unify context flexibility untouchables source2 source1
      (context2, var) <- lift $ Context.extendUnnamed context1 name2 source2
      domain2 <- lift $ Evaluation.evaluateClosure domainClosure2 $ Domain.var var
      context3 <- unify context2 flexibility (IntSet.insert var untouchables) domain1 domain2
      pure $ unextend context3

    (Domain.Fun source1 domain1, Domain.Fun source2 domain2) -> do
      context1 <- unify context flexibility untouchables source2 source1
      unify context1 flexibility untouchables domain1 domain2

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
        occurs context (IntSet.insert var untouchables) value
        lift $ Context.define context var value

unifyBranches
  :: Context v
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
  (Domain.Branches outerEnv2 branches2 defaultBranch2) = do
    let
      branches =
        HashMap.intersectionWith (,) branches1 branches2

      missing1 =
        HashMap.difference branches1 branches

      missing2 =
        HashMap.difference branches2 branches
    unless (HashMap.null missing1 && HashMap.null missing2) $
      throwError Dunno
    outerContext' <- foldM
      (\context -> uncurry $ unifyTele context outerEnv1 outerEnv2 outerUntouchables)
      outerContext
      branches
    case (defaultBranch1, defaultBranch2) of
      (Just branch1, Just branch2) -> do
        branch1' <- lift $ Evaluation.evaluate outerEnv1 branch1
        branch2' <- lift $ Evaluation.evaluate outerEnv2 branch2
        unify outerContext' flexibility outerUntouchables branch1' branch2'

      (Nothing, Nothing) ->
        pure outerContext'

      _ ->
        throwError Dunno
  where
    unifyTele
      :: Context v
      -> Domain.Environment v1
      -> Domain.Environment v2
      -> IntSet Var
      -> Telescope Syntax.Type Syntax.Term v1
      -> Telescope Syntax.Type Syntax.Term v2
      -> E M (Context v)
    unifyTele context env1 env2 untouchables tele1 tele2 =
      case (tele1, tele2) of
        (Telescope.Extend name1 type1 plicity1 tele1', Telescope.Extend _name2 type2 plicity2 tele2')
          | plicity1 == plicity2 -> do
            type1' <- lift $ Evaluation.evaluate env1 type1
            type2' <- lift $ Evaluation.evaluate env2 type2
            context' <- unify context flexibility untouchables type1' type2'
            (context'', var) <- lift $ Context.extendUnnamed context' name1 type1'
            context''' <-
              unifyTele
                context''
                (Environment.extendVar env1 var)
                (Environment.extendVar env2 var)
                (IntSet.insert var untouchables)
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

occurs :: Context v -> IntSet Var -> Domain.Value -> E M ()
occurs context untouchables value = do
  value' <- lift $ Context.forceHead context value
  case value' of
    Domain.Neutral (Domain.Var var) _
      | IntSet.member var untouchables ->
        throwError Dunno

    Domain.Glued (Domain.Var _) _ value'' ->
      occursForce value''

    Domain.Glued hd spine value'' ->
      occurs context untouchables (Domain.Neutral hd spine) `catchError` \_ ->
        occursForce value''

    Domain.Neutral _ spine ->
      mapM_ (occurs context untouchables . snd) spine

    Domain.Lam name type_ _ closure ->
      occursAbstraction name type_ closure

    Domain.Pi name source _ domainClosure ->
      occursAbstraction name source domainClosure

    Domain.Fun source domain -> do
      occurs context untouchables source
      occurs context untouchables domain

    Domain.Case scrutinee branches -> do
      occurs context untouchables scrutinee
      occursBranches context untouchables branches

  where
    occursForce lazyValue = do
      value' <- lift $ force lazyValue
      occurs context untouchables value'

    occursAbstraction name type_ closure = do
      occurs context untouchables type_
      (context', var) <- lift $ Context.extendUnnamed context name type_
      let
        varValue =
          Domain.var var

      body <- lift $ Evaluation.evaluateClosure closure varValue
      occurs context' untouchables body

occursBranches :: Context v -> IntSet Var -> Domain.Branches -> E M ()
occursBranches outerContext outerUntouchables (Domain.Branches outerEnv branches defaultBranch) = do
  forM_ branches $
    occursTele outerContext outerUntouchables outerEnv
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
        Telescope.Extend name type_ _plicity tele' -> do
          type' <- lift $ Evaluation.evaluate env type_
          (context'', var) <- lift $ Context.extendUnnamed context name type'
          occursTele
            context''
            (IntSet.insert var untouchables)
            (Environment.extendVar env var)
            tele'
        Telescope.Empty body -> do
          body' <- lift $ Evaluation.evaluate env body
          occurs context untouchables body'
