{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoFieldSelectors #-}

module Elaboration.Equation where

import Control.Exception.Lifted
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Syntax as Syntax
import qualified Data.HashSet as HashSet
import qualified Data.Tsil as Tsil
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import Elaboration.Depth (compareHeadDepths)
import qualified Environment
import Flexibility (Flexibility)
import qualified Flexibility
import Monad
import Protolude hiding (catch, force, throwIO)
import Telescope (Telescope)
import qualified Telescope

data Error
  = Nope
  | Dunno
  deriving (Eq, Ord, Show, Exception)

type Equate v = StateT (Context v) M

equate :: Context v -> Flexibility -> Domain.Value -> Domain.Value -> M (Context v)
equate context flexibility value1 value2 = do
  -- putText "Equating"
  -- Context.dumpValue context value1
  -- Context.dumpValue context value2
  execStateT
    (equateM flexibility value1 value2)
    context

contextual1 :: (Context v -> a -> M b) -> a -> Equate v b
contextual1 f x = do
  c <- get
  lift $ f c x

equateM :: Flexibility -> Domain.Value -> Domain.Value -> Equate v ()
equateM flexibility unforcedValue1 unforcedValue2 = go unforcedValue1 unforcedValue2
  where
    go value1 value2 = do
      value1' <- contextual1 Context.forceHeadGlue value1
      value2' <- contextual1 Context.forceHeadGlue value2
      case (value1', value2') of
        -- Glue
        (Domain.Glued head1 spine1 value1'', Domain.Glued head2 spine2 value2'')
          | head1 == head2 ->
              equateSpines Flexibility.Flexible spine1 spine2 `catch` \(_ :: Error) ->
                go value1'' value2''
          | otherwise -> do
              ordering <- lift $ compareHeadDepths head1 head2
              case ordering of
                LT -> go value1' value2''
                GT -> go value1'' value2'
                EQ -> go value1'' value2''
        (Domain.Glued _ _ value1'', _) ->
          go value1'' value2'
        (_, Domain.Glued _ _ value2'') ->
          go value1' value2''
        -- Same heads
        (Domain.AnyNeutral head1 spine1, Domain.AnyNeutral head2 spine2)
          | head1 == head2 -> do
              let flexibility' = max (Domain.headFlexibility head1) flexibility
              equateSpines flexibility' spine1 spine2
        (Domain.Con con1 args1, Domain.Con con2 args2)
          | con1 == con2
          , map fst args1 == map fst args2 ->
              Tsil.zipWithM_ (equateM flexibility `on` snd) args1 args2
          | otherwise ->
              throwIO Nope
        (Domain.Lit lit1, Domain.Lit lit2)
          | lit1 == lit2 ->
              pure ()
          | otherwise ->
              throwIO Nope
        (Domain.Fun domain1 plicity1 target1, Domain.Fun domain2 plicity2 target2)
          | plicity1 == plicity2 -> do
              equateM flexibility domain2 domain1
              equateM flexibility target1 target2

        -- Neutrals
        (Domain.AnyNeutral head1 spine1, Domain.AnyNeutral head2 spine2)
          | Flexibility.Rigid <- max (Domain.headFlexibility head1) flexibility
          , Flexibility.Rigid <- max (Domain.headFlexibility head2) flexibility -> do
              -- TODO: check both directions?
              ordering <- lift $ compareHeadDepths head1 head2
              case ordering of
                LT -> solve head2 spine2 unforcedValue1
                GT -> solve head1 spine1 unforcedValue2
                EQ -> solve head2 spine2 unforcedValue1
        (Domain.AnyNeutral head1 spine1, _)
          | Flexibility.Rigid <- max (Domain.headFlexibility head1) flexibility ->
              solve head1 spine1 unforcedValue2
        (_, Domain.AnyNeutral head2 spine2)
          | Flexibility.Rigid <- max (Domain.headFlexibility head2) flexibility ->
              solve head2 spine2 unforcedValue1
        _ ->
          throwIO Dunno

solve :: Domain.Head -> Domain.Spine -> Domain.Value -> Equate v ()
solve head_ spine value = do
  context <- get
  context' <- lift do
    value' <- Context.forceHead context value
    case value' of
      Domain.Con con _ -> do
        covered <- Context.coveredConstructors context head_ spine
        when (con `HashSet.member` covered) $
          throwIO Nope
      Domain.Lit lit -> do
        covered <- Context.coveredLiterals context head_ spine
        when (lit `HashSet.member` covered) $
          throwIO Nope
      _ -> pure ()
    occurs context (== head_) Flexibility.Rigid value
    occursSpine context isMeta Flexibility.Rigid spine
    Context.define context head_ spine value
  put context'
  where
    isMeta (Domain.Meta _) = True
    isMeta _ = False

equateSpines
  :: Flexibility
  -> Domain.Spine
  -> Domain.Spine
  -> Equate v ()
equateSpines flexibility spine1 spine2 =
  case (spine1, spine2) of
    (Domain.Empty, Domain.Empty) -> pure ()
    (Domain.App plicity1 arg1 Domain.:< spine1', Domain.App plicity2 arg2 Domain.:< spine2')
      | plicity1 == plicity2 -> do
          equateM flexibility arg1 arg2
          equateSpines flexibility spine1' spine2'
    _ ->
      throwIO Dunno

occurs :: Context v -> (Domain.Head -> Bool) -> Flexibility -> Domain.Value -> M ()
occurs context occ flexibility value = do
  value' <- Context.forceHeadGlue context value
  case value' of
    Domain.AnyNeutral hd spine -> do
      occursHead occ flexibility hd
      occursSpine context occ (max (Domain.headFlexibility hd) flexibility) spine
    Domain.Con _ args ->
      mapM_ (occurs context occ flexibility . snd) args
    Domain.Lit _ ->
      pure ()
    Domain.Glued (Domain.Var _) _ value'' -> do
      occurs context occ flexibility value''
    Domain.Glued hd spine value'' ->
      do
        occursHead occ Flexibility.Flexible hd
        occursSpine context occ Flexibility.Flexible spine
        `catch` \(_ :: Error) ->
          occurs context occ (max (Domain.headFlexibility hd) flexibility) value''
    Domain.Lazy lazyValue -> do
      value'' <- force lazyValue
      occurs context occ flexibility value''
    Domain.Lam bindings type_ _ closure ->
      occursAbstraction (Bindings.toName bindings) type_ closure
    Domain.Pi binding domain _ targetClosure ->
      occursAbstraction (Binding.toName binding) domain targetClosure
    Domain.Fun domain _ target -> do
      occurs context occ flexibility domain
      occurs context occ flexibility target
  where
    occursAbstraction name type_ closure = do
      occurs context occ flexibility type_
      (context', var) <- Context.extend context name type_
      let varValue = Domain.var var
      body <- Evaluation.evaluateClosure closure varValue
      occurs context' occ flexibility body

occursHead :: (Domain.Head -> Bool) -> Flexibility -> Domain.Head -> M ()
occursHead occ flexibility head_ =
  when (occ head_) $
    throwIO case flexibility of
      Flexibility.Rigid -> Nope
      Flexibility.Flexible -> Dunno

occursSpine :: Context v -> (Domain.Head -> Bool) -> Flexibility -> Domain.Spine -> M ()
occursSpine context occ flexibility =
  Domain.mapM_ $ occursElimination context occ flexibility

occursElimination :: Context v -> (Domain.Head -> Bool) -> Flexibility -> Domain.Elimination -> M ()
occursElimination context occ flexibility elimination =
  case elimination of
    Domain.App _plicity arg -> occurs context occ flexibility arg
    Domain.Case branches -> occursBranches context occ flexibility branches

occursBranches :: Context v -> (Domain.Head -> Bool) -> Flexibility -> Domain.Branches -> M ()
occursBranches context occ flexibility (Domain.Branches outerEnv branches defaultBranch) = do
  case branches of
    Syntax.ConstructorBranches _ constructorBranches ->
      forM_ constructorBranches $ mapM_ $ occursTele context outerEnv
    Syntax.LiteralBranches literalBranches ->
      forM_ literalBranches $
        mapM_ $
          occursTele context outerEnv . Telescope.Empty
  forM_ defaultBranch $
    occursTele context outerEnv . Telescope.Empty
  where
    occursTele
      :: Context v1
      -> Domain.Environment v2
      -> Telescope Bindings Syntax.Type Syntax.Term v2
      -> M ()
    occursTele context' env tele =
      case tele of
        Telescope.Extend bindings type_ _plicity tele' -> do
          type' <- Evaluation.evaluate env type_
          occurs context' occ flexibility type'
          (context'', var) <- Context.extend context (Bindings.toName bindings) type'
          occursTele context'' (Environment.extendVar env var) tele'
        Telescope.Empty body -> do
          body' <- Evaluation.evaluate env body
          occurs context' occ flexibility body'
