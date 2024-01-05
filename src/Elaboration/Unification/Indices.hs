{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoFieldSelectors #-}

module Elaboration.Unification.Indices where

import Control.Exception.Lifted
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Syntax as Syntax
import qualified Data.EnumMap as EnumMap
import qualified Data.IntSeq as IntSeq
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Tsil as Tsil
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import qualified Environment
import Flexibility (Flexibility)
import qualified Flexibility
import Index
import qualified Index.Map
import Monad
import Name (Name)
import Protolude hiding (catch, force, throwIO)
import Telescope (Telescope)
import qualified Telescope
import Var

data Error
  = Nope
  | Dunno
  deriving (Eq, Ord, Show, Exception)

data UnificationState v = UnificationState
  { context :: !(Context v)
  , touchableBefore :: !(Index (Succ v))
  }

type Unify v = StateT (UnificationState v) M

unify :: Context v -> Flexibility -> Domain.Value -> Domain.Value -> M (Context v)
unify context flexibility value1 value2 =
  (.context)
    <$> execStateT
      (unifyM flexibility value1 value2)
      UnificationState
        { context = context
        , touchableBefore = Index.Zero
        }

isTouchable :: Var -> Unify v Bool
isTouchable var = do
  touchableIndex <- gets (.touchableBefore)
  context <- gets (.context)
  pure case Context.lookupVarIndex var context of
    Just varIndex -> Index.Succ varIndex > touchableIndex
    Nothing -> False

extend :: Name -> Domain.Type -> (Var -> Unify (Succ v) a) -> Unify v a
extend name type_ k = do
  st <- get
  (result, st') <- lift do
    (context', var) <- Context.extend st.context name type_
    runStateT (k var) st {context = context', touchableBefore = Index.Succ st.touchableBefore}
  put st' {context = unextend st'.context, touchableBefore = st.touchableBefore}
  pure result

unextend :: Context (Succ v) -> Context v
unextend context =
  case (context.indices, context.boundVars) of
    (indices Index.Map.:> var, boundVars IntSeq.:> _) ->
      context
        { Context.varNames = EnumMap.delete var context.varNames
        , Context.indices = indices
        , Context.types = EnumMap.delete var context.types
        , Context.boundVars = boundVars
        }
    _ ->
      panic "Unification.Indices.unextend"

contextual1 :: (Context v -> a -> M b) -> a -> Unify v b
contextual1 f x = do
  c <- gets (.context)
  lift $ f c x

contextual2 :: (Context v -> a -> b -> M c) -> a -> b -> Unify v c
contextual2 f x y = do
  c <- gets (.context)
  lift $ f c x y

unifyM :: Flexibility -> Domain.Value -> Domain.Value -> Unify v ()
unifyM flexibility value1 value2 = do
  value1' <- contextual1 Context.forceHeadGlue value1
  value2' <- contextual1 Context.forceHeadGlue value2
  case (value1', value2') of
    -- Same heads
    (Domain.Neutral head1 spine1, Domain.Neutral head2 spine2)
      | head1 == head2 -> do
          let flexibility' = max (Domain.headFlexibility head1) flexibility
          unifySpines flexibility' spine1 spine2
    (Domain.Con con1 args1, Domain.Con con2 args2)
      | con1 == con2
      , map fst args1 == map fst args2 ->
          Tsil.zipWithM_ (unifyM flexibility `on` snd) args1 args2
      | otherwise ->
          throwIO Nope
    (Domain.Lit lit1, Domain.Lit lit2)
      | lit1 == lit2 ->
          pure ()
      | otherwise ->
          throwIO Nope
    (Domain.Glued head1 spine1 value1'', Domain.Glued head2 spine2 value2'')
      | head1 == head2 ->
          unifySpines Flexibility.Flexible spine1 spine2 `catch` \(_ :: Error) ->
            unifyM flexibility value1'' value2''
    (Domain.Glued _ _ value1'', _) ->
      unifyM flexibility value1'' value2'
    (_, Domain.Glued _ _ value2'') ->
      unifyM flexibility value1' value2''
    (Domain.Lam bindings1 type1 plicity1 closure1, Domain.Lam _ type2 plicity2 closure2)
      | plicity1 == plicity2 ->
          unifyAbstraction (Bindings.toName bindings1) type1 closure1 type2 closure2
    (Domain.Pi binding1 domain1 plicity1 targetClosure1, Domain.Pi _ domain2 plicity2 targetClosure2)
      | plicity1 == plicity2 ->
          unifyAbstraction (Binding.toName binding1) domain1 targetClosure1 domain2 targetClosure2
    (Domain.Pi binding1 domain1 plicity1 targetClosure1, Domain.Fun domain2 plicity2 target2)
      | plicity1 == plicity2 -> do
          unifyM flexibility domain2 domain1
          extend (Binding.toName binding1) domain1 \var -> do
            target1 <- lift $ Evaluation.evaluateClosure targetClosure1 $ Domain.var var
            unifyM flexibility target1 target2
    (Domain.Fun domain1 plicity1 target1, Domain.Pi binding2 domain2 plicity2 targetClosure2)
      | plicity1 == plicity2 -> do
          unifyM flexibility domain2 domain1
          extend (Binding.toName binding2) domain2 \var -> do
            target2 <- lift $ Evaluation.evaluateClosure targetClosure2 $ Domain.var var
            unifyM flexibility target1 target2
    (Domain.Fun domain1 plicity1 target1, Domain.Fun domain2 plicity2 target2)
      | plicity1 == plicity2 -> do
          unifyM flexibility domain2 domain1
          unifyM flexibility target1 target2

    -- Eta expand
    (Domain.Lam bindings1 type1 plicity1 closure1, v2) ->
      extend (Bindings.toName bindings1) type1 \var -> do
        let varValue = Domain.var var
        body1 <- lift $ Evaluation.evaluateClosure closure1 varValue
        body2 <- lift $ Evaluation.apply v2 plicity1 varValue
        unifyM flexibility body1 body2
    (v1, Domain.Lam bindings2 type2 plicity2 closure2) ->
      extend (Bindings.toName bindings2) type2 \var -> do
        let varValue = Domain.var var
        body1 <- lift $ Evaluation.apply v1 plicity2 varValue
        body2 <- lift $ Evaluation.evaluateClosure closure2 varValue
        unifyM flexibility body1 body2

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
    unifyAbstraction name type1 closure1 type2 closure2 = do
      unifyM flexibility type1 type2

      extend name type1 \var -> do
        let varValue = Domain.var var
        body1 <- lift $ Evaluation.evaluateClosure closure1 varValue
        body2 <- lift $ Evaluation.evaluateClosure closure2 varValue
        unifyM flexibility body1 body2

    solve var value = do
      touchable <- isTouchable var
      if touchable
        then do
          occurs var Flexibility.Rigid value
          context' <- contextual2 Context.define var value
          modify \st -> st {context = context'}
        else throwIO Dunno

unifySpines
  :: Flexibility
  -> Domain.Spine
  -> Domain.Spine
  -> Unify v ()
unifySpines flexibility spine1 spine2 =
  case (spine1, spine2) of
    (Domain.Empty, Domain.Empty) -> pure ()
    (spine1' Domain.:> elimination1, spine2' Domain.:> elimination2) -> do
      unifySpines flexibility spine1' spine2'
      case (elimination1, elimination2) of
        (Domain.App plicity1 arg1, Domain.App plicity2 arg2)
          | plicity1 == plicity2 -> unifyM flexibility arg1 arg2
        (Domain.Case branches1, Domain.Case branches2) ->
          unifyBranches flexibility branches1 branches2
        _ ->
          throwIO Dunno
    _ ->
      throwIO Dunno

unifyBranches :: Flexibility -> Domain.Branches -> Domain.Branches -> Unify v ()
unifyBranches
  flexibility
  (Domain.Branches outerEnv1 branches1 defaultBranch1)
  (Domain.Branches outerEnv2 branches2 defaultBranch2) =
    case (branches1, branches2) of
      (Syntax.ConstructorBranches conTypeName1 conBranches1, Syntax.ConstructorBranches conTypeName2 conBranches2)
        | conTypeName1 == conTypeName2 ->
            unifyMaps conBranches1 conBranches2
      (Syntax.LiteralBranches litBranches1, Syntax.LiteralBranches litBranches2) ->
        unifyMaps (second Telescope.Empty <$> litBranches1) (second Telescope.Empty <$> litBranches2)
      _ ->
        throwIO Dunno
    where
      unifyMaps brs1 brs2 = do
        let branches = OrderedHashMap.intersectionWith (,) brs1 brs2
            extras1 = OrderedHashMap.difference brs1 branches
            extras2 = OrderedHashMap.difference brs2 branches

        when
          ( (not (OrderedHashMap.null extras1) && isNothing defaultBranch2)
              || (not (OrderedHashMap.null extras2) && isNothing defaultBranch1)
          )
          $ throwIO Dunno

        defaultBranch1' <- forM defaultBranch1 $ lift . Evaluation.evaluate outerEnv1
        defaultBranch2' <- forM defaultBranch2 $ lift . Evaluation.evaluate outerEnv2

        forM_ defaultBranch2' \branch2 ->
          forM_ extras1 \(_, tele1) ->
            withInstantiatedTele outerEnv1 tele1 \branch1 -> do
              unifyM flexibility branch1 branch2

        forM_ defaultBranch1' \branch1 ->
          forM_ extras2 \(_, tele2) ->
            withInstantiatedTele outerEnv2 tele2 \branch2 ->
              unifyM flexibility branch1 branch2

        forM_ branches \((_, tele1), (_, tele2)) ->
          unifyTele outerEnv1 outerEnv2 tele1 tele2

        case (defaultBranch1', defaultBranch2') of
          (Just branch1, Just branch2) ->
            unifyM flexibility branch1 branch2
          _ ->
            pure ()

      unifyTele
        :: Domain.Environment v1
        -> Domain.Environment v2
        -> Telescope Bindings Syntax.Type Syntax.Term v1
        -> Telescope Bindings Syntax.Type Syntax.Term v2
        -> Unify v ()
      unifyTele env1 env2 tele1 tele2 =
        case (tele1, tele2) of
          (Telescope.Extend bindings1 type1 plicity1 tele1', Telescope.Extend _bindings2 type2 plicity2 tele2')
            | plicity1 == plicity2 -> do
                type1' <- lift $ Evaluation.evaluate env1 type1
                type2' <- lift $ Evaluation.evaluate env2 type2
                unifyM flexibility type1' type2'
                extend (Bindings.toName bindings1) type1' \var ->
                  unifyTele
                    (Environment.extendVar env1 var)
                    (Environment.extendVar env2 var)
                    tele1'
                    tele2'
          (Telescope.Empty body1, Telescope.Empty body2) -> do
            body1' <- lift $ Evaluation.evaluate env1 body1
            body2' <- lift $ Evaluation.evaluate env2 body2
            unifyM flexibility body1' body2'
          _ ->
            panic "unifyTele"

withInstantiatedTele
  :: Domain.Environment v1
  -> Telescope Bindings Syntax.Type Syntax.Term v1
  -> (forall v'. Domain.Value -> Unify v' k)
  -> Unify v k
withInstantiatedTele env tele k =
  case tele of
    Telescope.Empty body -> do
      body' <- lift $ Evaluation.evaluate env body
      k body'
    Telescope.Extend bindings type_ _plicity tele' -> do
      type' <- lift $ Evaluation.evaluate env type_
      extend (Bindings.toName bindings) type' \var ->
        withInstantiatedTele (Environment.extendVar env var) tele' k

occurs :: Var -> Flexibility -> Domain.Value -> Unify v ()
occurs occ flexibility value = do
  value' <- contextual1 Context.forceHeadGlue value
  case value' of
    Domain.Neutral hd spine -> do
      occursHead occ flexibility hd
      Domain.mapM_ (occursElimination occ (max (Domain.headFlexibility hd) flexibility)) spine
    Domain.Con _ args ->
      mapM_ (occurs occ flexibility . snd) args
    Domain.Lit _ ->
      pure ()
    Domain.Glued (Domain.Var _) _ value'' ->
      occurs occ flexibility value''
    Domain.Lazy lazyValue -> do
      value'' <- lift $ force lazyValue
      occurs occ flexibility value''
    Domain.Glued hd spine value'' ->
      occurs occ Flexibility.Flexible (Domain.Neutral hd spine) `catch` \(_ :: Error) ->
        occurs occ flexibility value''
    Domain.Lam bindings type_ _ closure ->
      occursAbstraction (Bindings.toName bindings) type_ closure
    Domain.Pi binding domain _ targetClosure ->
      occursAbstraction (Binding.toName binding) domain targetClosure
    Domain.Fun domain _ target -> do
      occurs occ flexibility domain
      occurs occ flexibility target
  where
    occursAbstraction name type_ closure = do
      occurs occ flexibility type_
      extend name type_ \var -> do
        let varValue = Domain.var var
        body <- lift $ Evaluation.evaluateClosure closure varValue
        occurs occ flexibility body

occursHead :: Var -> Flexibility -> Domain.Head -> Unify v ()
occursHead occ flexibility hd =
  case hd of
    Domain.Var var
      | var == occ ->
          throwIO case flexibility of
            Flexibility.Rigid -> Nope
            Flexibility.Flexible -> Dunno
      | otherwise -> do
          touchable <- isTouchable var
          unless touchable $
            throwIO case flexibility of
              Flexibility.Rigid -> Nope
              Flexibility.Flexible -> Dunno
    Domain.Global _ -> pure ()
    Domain.Meta _ -> pure ()

occursElimination
  :: Var
  -> Flexibility
  -> Domain.Elimination
  -> Unify v ()
occursElimination occ flexibility elimination =
  case elimination of
    Domain.App _plicity arg -> occurs occ flexibility arg
    Domain.Case branches -> occursBranches occ flexibility branches

occursBranches
  :: Var
  -> Flexibility
  -> Domain.Branches
  -> Unify v ()
occursBranches occ flexibility (Domain.Branches outerEnv branches defaultBranch) = do
  case branches of
    Syntax.ConstructorBranches _ constructorBranches ->
      forM_ constructorBranches $ mapM_ $ occursTele outerEnv
    Syntax.LiteralBranches literalBranches ->
      forM_ literalBranches $
        mapM_ \branch ->
          occursTele outerEnv $ Telescope.Empty branch
  forM_ defaultBranch \branch ->
    occursTele outerEnv $ Telescope.Empty branch
  where
    occursTele
      :: Domain.Environment v1
      -> Telescope Bindings Syntax.Type Syntax.Term v1
      -> Unify v ()
    occursTele env tele =
      case tele of
        Telescope.Extend bindings type_ _plicity tele' -> do
          type' <- lift $ Evaluation.evaluate env type_
          occurs occ flexibility type'
          extend (Bindings.toName bindings) type' \var ->
            occursTele
              (Environment.extendVar env var)
              tele'
        Telescope.Empty body -> do
          body' <- lift $ Evaluation.evaluate env body
          occurs occ flexibility body'
