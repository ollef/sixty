{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Elaboration.Unification where

import qualified Builtin
import Control.Exception.Lifted
import Control.Monad.Zip
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Readback as Readback
import qualified Core.Syntax as Syntax
import qualified Data.EnumSet as EnumSet
import qualified Data.HashSet as HashSet
import Data.IntSeq (IntSeq)
import qualified Data.IntSeq as IntSeq
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Sequence as Seq
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import {-# SOURCE #-} qualified Elaboration
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import Elaboration.Depth (compareHeadDepths)
import qualified Elaboration.Equation as Equation
import qualified Elaboration.Meta as Meta
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
import Protolude hiding (catch, check, evaluate, force, head, throwIO, try)
import qualified Query
import Rock
import Telescope (Telescope)
import qualified Telescope
import Var

tryUnify :: Context v -> Domain.Value -> Domain.Value -> M (Syntax.Term v -> Syntax.Term v)
tryUnify context value1 value2 = do
  success <- Context.try_ context $ unify context Flexibility.Rigid value1 value2
  if success
    then pure identity
    else do
      type_ <- Readback.readback (Context.toEnvironment context) value2
      pure $ const $ Builtin.unknown type_

tryUnifyD :: Context v -> Domain.Value -> Domain.Value -> M (Domain.Value -> Domain.Value)
tryUnifyD context value1 value2 = do
  success <- Context.try_ context $ unify context Flexibility.Rigid value1 value2
  pure
    if success
      then identity
      else const $ Builtin.Unknown value2

unify :: Context v -> Flexibility -> Domain.Value -> Domain.Value -> M ()
unify context flexibility unforcedValue1 unforcedValue2 = catchAndAdd $ go unforcedValue1 unforcedValue2
  where
    go value1 value2 = do
      value1' <- Context.forceHeadGlue context value1
      value2' <- Context.forceHeadGlue context value2
      -- putText "unifying"
      -- Context.dumpValue context value1'
      -- Context.dumpValue context value2'
      case (value1', value2') of
        -- Glued values
        (Domain.Glued head1 (Domain.Apps args1) value1'', Domain.Glued head2 (Domain.Apps args2) value2'')
          | head1 == head2
          , (fst <$> args1) == (fst <$> args2) ->
              sequence_ (Seq.zipWith (unify context Flexibility.Flexible `on` snd) args1 args2) `catch` \(_ :: Error.Elaboration) ->
                unify context flexibility value1'' value2''
          | otherwise -> do
              ordering <- compareHeadDepths head1 head2
              case ordering of
                LT -> go value1' value2''
                GT -> go value1'' value2'
                EQ -> go value1'' value2''
        (Domain.Glued _ _ value1'', _) ->
          go value1'' value2'
        (_, Domain.Glued _ _ value2'') ->
          go value1' value2''
        -- Both metas
        (Domain.AnyNeutral (Domain.Meta metaIndex1) (Domain.Apps args1), Domain.AnyNeutral (Domain.Meta metaIndex2) (Domain.Apps args2))
          | Flexibility.Rigid <- flexibility -> do
              args1' <- mapM (mapM $ Context.forceHead context) args1
              args2' <- mapM (mapM $ Context.forceHead context) args2
              if metaIndex1 == metaIndex2 && map fst args1 == map fst args2
                then do
                  -- Intersection: If the same metavar is applied to two different lists of unknown
                  -- variables its solution must not mention any variables at
                  -- positions where the lists differ.
                  let keep =
                        mzipWith (shouldKeepMetaArgument `on` snd) args1' args2'
                  if and keep
                    then sequence_ $ Seq.zipWith (unify context flexibility `on` snd) args1 args2
                    else pruneMeta context metaIndex1 keep
                else do
                  let maybeUniqueVars1 = do
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
                          solve context metaIndex1 vars1 unforcedValue2
                      | otherwise ->
                          solve context metaIndex2 vars2 unforcedValue1
                    (Just vars1, _) ->
                      solve context metaIndex1 vars1 unforcedValue2
                    (_, Just vars2) ->
                      solve context metaIndex2 vars2 unforcedValue1
                    _ ->
                      can'tUnify

        -- Same heads
        (Domain.AnyNeutral head1 (Domain.Apps args1), Domain.AnyNeutral head2 (Domain.Apps args2))
          | head1 == head2
          , (fst <$> args1) == (fst <$> args2) -> do
              let flexibility' =
                    max (Domain.headFlexibility head1) flexibility
              sequence_ $ Seq.zipWith (unify context flexibility' `on` snd) args1 args2
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
          let varValue =
                Domain.var var

          body1 <- Evaluation.evaluateClosure closure1 varValue
          body2 <- Evaluation.apply v2 plicity1 varValue

          unify context' flexibility body1 body2
        (v1, Domain.Lam bindings2 type2 plicity2 closure2) -> do
          (context', var) <- Context.extend context (Bindings.toName bindings2) type2
          let varValue =
                Domain.var var

          body1 <- Evaluation.apply v1 plicity2 varValue
          body2 <- Evaluation.evaluateClosure closure2 varValue

          unify context' flexibility body1 body2

        -- Metas
        (Domain.Neutral (Domain.Meta metaIndex1) (Domain.Apps args1), _)
          | Flexibility.Rigid <- flexibility -> do
              args1' <- mapM (mapM $ Context.forceHead context) args1
              case traverse (traverse Domain.singleVarView) args1' of
                Just vars1
                  | unique $ snd <$> vars1 ->
                      solve context metaIndex1 vars1 unforcedValue2
                _ ->
                  can'tUnify
        (_, Domain.Neutral (Domain.Meta metaIndex2) (Domain.Apps args2))
          | Flexibility.Rigid <- flexibility -> do
              args2' <- mapM (mapM $ Context.forceHead context) args2
              case traverse (traverse Domain.singleVarView) args2' of
                Just vars2
                  | unique $ snd <$> vars2 ->
                      solve context metaIndex2 vars2 unforcedValue1
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
        (Domain.AnyNeutral head1 spine1@(Domain.Spine args1 ((branches1, _) Seq.:<| _)), Domain.AnyNeutral head2 spine2)
          | head1 == head2 ->
              unifySpines context Flexibility.Flexible spine1 spine2 `catch` \(_ :: Error.Elaboration) ->
                withBranches context head1 args1 branches1 \context' -> unify context' flexibility value1' value2
        (Domain.AnyNeutral head (Domain.Spine args ((branches, _) Seq.:<| _)), _) ->
          withBranches context head args branches \context' -> unify context' flexibility value1' value2
        (_, Domain.AnyNeutral head (Domain.Spine args ((branches, _) Seq.:<| _))) ->
          withBranches context head args branches \context' -> unify context' flexibility value1 value2'
        -- Failure terms mean that there has been an earlier error that's already
        -- been reported, so let's not trigger more errors from them.
        (Domain.Neutral (Domain.Global Builtin.UnknownName) _, _) ->
          pure ()
        (_, Domain.Neutral (Domain.Global Builtin.UnknownName) _) ->
          pure ()
        _ ->
          can'tUnify

    unifyAbstraction name type1 closure1 type2 closure2 = do
      unify context flexibility type1 type2

      (context', var) <- Context.extend context name type1
      let varValue =
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
          go unforcedValue1 unforcedValue2
        [Just (Right lit)] -> do
          unify context flexibility (Domain.Neutral (Domain.Meta meta) spine) $ Domain.Lit lit
          go unforcedValue1 unforcedValue2
        _ ->
          can'tUnify

    catchAndAdd m =
      case flexibility of
        Flexibility.Rigid ->
          m `catch` \err ->
            case err of
              Error.TypeMismatch stack -> do
                term1 <- Elaboration.readback context unforcedValue1
                term2 <- Elaboration.readback context unforcedValue2
                pterm1 <- Context.toPrettyableTerm context term1
                pterm2 <- Context.toPrettyableTerm context term2
                throwIO $
                  Error.TypeMismatch $
                    stack
                      Tsil.:> ( pterm1
                              , pterm2
                              )
              Error.OccursCheck stack -> do
                term1 <- Elaboration.readback context unforcedValue1
                term2 <- Elaboration.readback context unforcedValue2
                pterm1 <- Context.toPrettyableTerm context term1
                pterm2 <- Context.toPrettyableTerm context term2
                throwIO $
                  Error.OccursCheck $
                    stack
                      Tsil.:> ( pterm1
                              , pterm2
                              )
              _ ->
                throwIO err
        Flexibility.Flexible ->
          m

    can'tUnify =
      throwIO $ Error.TypeMismatch mempty

equalSpines :: Context v -> Domain.Spine -> Domain.Spine -> M Bool
equalSpines context spine1 spine2 =
  (True <$ unifySpines context Flexibility.Flexible spine1 spine2)
    `catch` \(_ :: Error.Elaboration) -> pure False

-------------------------------------------------------------------------------
-- Branch unification

withBranches :: Context v -> Domain.Head -> Domain.Args -> Domain.Branches -> (forall v'. Context v' -> M ()) -> M ()
withBranches context head args (Domain.Branches env brs maybeDefaultBranch) k =
  case brs of
    Syntax.ConstructorBranches typeName cbrs -> do
      headType_ <- typeOfHead context head
      type_ <- Context.instantiateType context headType_ args
      type' <- Context.forceHead context type_
      case type' of
        Domain.Neutral (Domain.Global typeName') (Domain.Apps typeArgs) | typeName == typeName' -> do
          covered <- Context.coveredConstructors context head $ Domain.Apps args
          forM_ (OrderedHashMap.toList cbrs) \(constr, (_, tele)) -> do
            let qconstr = Name.QualifiedConstructor typeName constr
            unless (HashSet.member qconstr covered) $
              withConstructorBranch context env head args qconstr (first implicitise <$> Tsil.fromSeq typeArgs) tele k
          when (isJust maybeDefaultBranch) do
            let covered' = HashSet.map (Name.QualifiedConstructor typeName) $ HashSet.fromMap (void $ OrderedHashMap.toMap cbrs)
            let context' = Context.withCoveredConstructors context head (Domain.Apps args) covered'
            k context'
        _ -> panic "withBranches type mismatch"
    Syntax.LiteralBranches lbrs -> do
      covered <- Context.coveredLiterals context head $ Domain.Apps args
      forM_ (OrderedHashMap.keys lbrs) \lit -> do
        unless (HashSet.member lit covered) do
          context' <- Context.define context head (Domain.Apps args) $ Domain.Lit lit
          k context'
      when (isJust maybeDefaultBranch) do
        let covered' = HashSet.fromMap $ void $ OrderedHashMap.toMap lbrs
        let context' = Context.withCoveredLiterals context head (Domain.Apps args) covered'
        k context'

-- TODO use Core.TypeOf.typeOfHead
typeOfHead :: Context v -> Domain.Head -> M Domain.Type
typeOfHead context hd =
  case hd of
    Domain.Var var ->
      pure $ Context.lookupVarType var context
    Domain.Global global -> do
      type_ <- fetch $ Query.ElaboratedType global
      Evaluation.evaluate Environment.empty type_
    Domain.Meta index -> do
      solution <- Context.lookupMeta context index
      Evaluation.evaluate Environment.empty $ Meta.entryType solution

withConstructorBranch
  :: Context v
  -> Domain.Environment v1
  -> Domain.Head
  -> Domain.Args
  -> Name.QualifiedConstructor
  -> Tsil (Plicity, Domain.Value)
  -> Telescope Bindings Syntax.Type Syntax.Term v1
  -> (forall v'. Context v' -> M ())
  -> M ()
withConstructorBranch context env head args constr constrArgs tele k =
  case tele of
    Telescope.Empty _ -> do
      let constrValue = Domain.Con constr constrArgs
      maybeBranchContext <- case constrValue of
        Builtin.Refl _ value1 value2 -> do
          result <- try $ Equation.equate context Flexibility.Rigid value1 value2
          pure case result of
            Left Equation.Nope -> Nothing
            Left Equation.Dunno -> Just context
            Right context' -> Just context'
        _ -> pure $ Just context
      case maybeBranchContext of
        Nothing -> pure ()
        Just context' -> do
          context'' <- Context.define context' head (Domain.Apps args) $ Domain.Con constr constrArgs
          k context''
    Telescope.Extend bindings type_ plicity tele' -> do
      type' <- Evaluation.evaluate env type_
      (context', var) <- Context.extend context (Bindings.toName bindings) type'
      withConstructorBranch
        context'
        (Environment.extendVar env var)
        head
        args
        constr
        (constrArgs Tsil.:> (plicity, Domain.var var))
        tele'
        k

-------------------------------------------------------------------------------
-- Spine unification

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
            unifyMaps conBranches1 conBranches2
      (Syntax.LiteralBranches litBranches1, Syntax.LiteralBranches litBranches2) ->
        unifyMaps (second Telescope.Empty <$> litBranches1) (second Telescope.Empty <$> litBranches2)
      _ ->
        can'tUnify
    where
      unifyMaps brs1 brs2 = do
        let branches = OrderedHashMap.intersectionWith (,) brs1 brs2
            extras1 = OrderedHashMap.difference brs1 branches
            extras2 = OrderedHashMap.difference brs2 branches

        when
          ( (not (OrderedHashMap.null extras1) && isNothing defaultBranch2)
              || (not (OrderedHashMap.null extras2) && isNothing defaultBranch1)
          )
          can'tUnify

        defaultBranch1' <- forM defaultBranch1 $ Evaluation.evaluate outerEnv1
        defaultBranch2' <- forM defaultBranch2 $ Evaluation.evaluate outerEnv2

        forM_ defaultBranch2' \branch2 ->
          forM_ extras1 \(_, tele1) ->
            withInstantiatedTele outerContext outerEnv1 tele1 \context' branch1 -> do
              unify context' flexibility branch1 branch2

        forM_ defaultBranch1' \branch1 ->
          forM_ extras2 \(_, tele2) ->
            withInstantiatedTele outerContext outerEnv2 tele2 \context' branch2 ->
              unify context' flexibility branch1 branch2

        forM_ branches \((_, tele1), (_, tele2)) ->
          unifyTele outerContext outerEnv1 outerEnv2 tele1 tele2

        case (defaultBranch1', defaultBranch2') of
          (Just branch1, Just branch2) ->
            unify outerContext flexibility branch1 branch2
          _ ->
            pure ()

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

withInstantiatedTele
  :: Context v
  -> Domain.Environment v1
  -> Telescope Bindings Syntax.Type Syntax.Term v1
  -> (forall v'. Context v' -> Domain.Value -> M k)
  -> M k
withInstantiatedTele context env tele k =
  case tele of
    Telescope.Empty body -> do
      body' <- Evaluation.evaluate env body
      k context body'
    Telescope.Extend bindings type_ _plicity tele' -> do
      type' <- Evaluation.evaluate env type_
      (context', var) <- Context.extend context (Bindings.toName bindings) type'
      withInstantiatedTele context' (Environment.extendVar env var) tele' k

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
  defaultBranch' <-
    catMaybes . toList
      <$> forM defaultBranch \branch -> do
        isMatch <- branchMatches outerContext resultValue' outerEnv $ Telescope.Empty branch
        pure
          if isMatch
            then Just Nothing
            else Nothing

  branches' <- fmap
    catMaybes
    case branches of
      Syntax.ConstructorBranches constructorTypeName constructorBranches ->
        forM (OrderedHashMap.toList constructorBranches) \(constr, (_, tele)) -> do
          isMatch <- branchMatches outerContext resultValue' outerEnv tele
          pure
            if isMatch
              then Just $ Just $ Left $ Name.QualifiedConstructor constructorTypeName constr
              else Nothing
      Syntax.LiteralBranches literalBranches ->
        forM (OrderedHashMap.toList literalBranches) \(int, (_, branch)) -> do
          isMatch <- branchMatches outerContext resultValue' outerEnv $ Telescope.Empty branch
          pure
            if isMatch
              then Just $ Just $ Right int
              else Nothing

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
            (Domain.AnyNeutral _ (_ Domain.:> Domain.Case branches'), _) -> do
              matches <- potentiallyMatchingBranches context resultValue branches'
              pure $ not $ null matches
            (Domain.AnyNeutral head1 (Domain.Apps _), Domain.AnyNeutral head2 (Domain.Apps _)) ->
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
  -> Seq (Plicity, Domain.Value)
  -> M Domain.Type
instantiatedMetaType context meta args = do
  solution <- Context.lookupMeta context meta
  case solution of
    Meta.Unsolved metaType _ _ _ -> do
      metaType' <- Evaluation.evaluate Environment.empty metaType
      Context.instantiateType context metaType' args
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
          Environment.empty
          (Syntax.fromVoid $ Telescope.fold Syntax.Pi constrType)
      instantiatedConstrType <- Context.instantiateType context constrType' typeArgs
      (metas, _) <- Elaboration.insertMetas context Elaboration.UntilTheEnd instantiatedConstrType
      pure $ Domain.Con constr $ Tsil.fromSeq typeArgs <> fromList metas
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
        Domain.AnyNeutral hd Domain.Empty ->
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
solve :: Context v -> Meta.Index -> Seq (Plicity, Var) -> Domain.Value -> M ()
solve context meta vars value = do
  term <- checkSolution context meta vars value
  Context.solveMeta context meta term

-- | Occurs check, scope check, prune, and read back the solution at the same
-- time.
checkSolution
  :: Context v
  -> Meta.Index
  -> Seq (Plicity, Var)
  -> Domain.Value
  -> M (Syntax.Term Void)
checkSolution outerContext meta vars value = do
  let indices = IntSeq.fromSeq $ snd <$> vars
      renaming =
        PartialRenaming
          { occurs = Just meta
          , environment =
              (Context.toEnvironment outerContext)
                { Environment.indices = Index.Map indices
                , Environment.glueableBefore = Index $ IntSeq.length indices
                }
          , renamingFlexibility = Flexibility.Rigid
          }
  solution <- renameValue outerContext renaming value
  addAndRenameLambdas outerContext meta (fst <$> vars) indices solution

data PartialRenaming v' = PartialRenaming
  { occurs :: Maybe Meta.Index
  , environment :: !(Domain.Environment v')
  , renamingFlexibility :: !Flexibility
  }

addAndRenameLambdas
  :: Context v
  -> Meta.Index
  -> Seq Plicity
  -> IntSeq Var
  -> Syntax.Term v'
  -> M (Syntax.Term v')
addAndRenameLambdas outerContext meta plicities vars term =
  case (plicities, vars) of
    (Seq.Empty, IntSeq.Empty) ->
      pure term
    (plicities' Seq.:|> plicity, vars' IntSeq.:> var) -> do
      let name =
            Context.lookupVarName var outerContext
          type_ =
            Context.lookupVarType var outerContext
          renaming =
            PartialRenaming
              { occurs = Just meta
              , environment =
                  (Context.toEnvironment outerContext)
                    { Environment.indices = Index.Map vars'
                    , Environment.glueableBefore = Index $ IntSeq.length vars'
                    }
              , renamingFlexibility = Flexibility.Rigid
              }

      type' <- renameValue outerContext renaming type_
      let term' =
            Syntax.Lam (Bindings.Unspanned name) type' plicity (Syntax.succ term)
      addAndRenameLambdas outerContext meta plicities' vars' term'
    _ ->
      panic "addAndRenameLambdas length mismatch"

renameValue
  :: Context v
  -> PartialRenaming v'
  -> Domain.Value
  -> M (Syntax.Term v')
renameValue outerContext renaming value = do
  value' <- Context.forceHeadGlue outerContext value
  case value' of
    Domain.AnyNeutral (Domain.Var var) spine ->
      case Environment.lookupVarIndex var $ environment renaming of
        Nothing ->
          throwIO $ Error.TypeMismatch mempty
        Just i ->
          renameSpine outerContext renaming (Syntax.Var i) spine
    Domain.AnyNeutral (Domain.Global global) spine ->
      renameSpine outerContext renaming (Syntax.Global global) spine
    Domain.AnyNeutral (Domain.Meta meta) spine
      | Just meta == occurs renaming ->
          throwIO $ Error.OccursCheck mempty
      | otherwise ->
          case spine of
            Domain.Apps args
              | Flexibility.Rigid <- renamingFlexibility renaming -> do
                  args' <- mapM (Context.forceHead outerContext . snd) args
                  case traverse Domain.singleVarView args' of
                    Just vars
                      | allowedVars <- map (\v -> isJust (Environment.lookupVarIndex v $ environment renaming) && isNothing (Environment.lookupVarValue v $ environment renaming)) vars
                      , any not allowedVars ->
                          do
                            pruneMeta outerContext meta allowedVars
                            renameValue outerContext renaming $ Domain.Neutral (Domain.Meta meta) spine
                    _ ->
                      renameSpine outerContext renaming (Syntax.Meta meta) spine
            _ ->
              renameSpine outerContext renaming (Syntax.Meta meta) spine
    Domain.Con con args ->
      Syntax.apps (Syntax.Con con) <$> mapM (mapM $ renameValue outerContext renaming) args
    Domain.Lit lit ->
      pure $ Syntax.Lit lit
    Domain.Glued (Domain.Global global) spine value'' ->
      renameSpine outerContext renaming {renamingFlexibility = Flexibility.Flexible} (Syntax.Global global) spine `catch` \(_ :: Error.Elaboration) -> do
        renameValue outerContext renaming value''
    Domain.Glued (Domain.Meta meta) spine value'' -> do
      case occurs renaming of
        Just occursMeta -> do
          metas <- Context.metaSolutionMetas outerContext meta
          if EnumSet.member occursMeta metas
            then -- The meta solution might contain `occurs`, so we need to force.
              renameValue outerContext renaming value''
            else -- The solved meta (`meta`) doesn't contain the meta we're solving
            -- (`occursMeta`) in scope, so we can try without unfolding
            -- `meta`.

              renameSpine outerContext renaming {renamingFlexibility = Flexibility.Flexible} (Syntax.Meta meta) spine `catch` \(_ :: Error.Elaboration) ->
                renameValue outerContext renaming value''
        Nothing ->
          renameValue outerContext renaming value''
    Domain.Glued (Domain.Var _) _ value'' ->
      -- The variable's value might contain `occurs`, so we need to force
      renameValue outerContext renaming value''
    Domain.Lazy lazyValue -> do
      value'' <- force lazyValue
      renameValue outerContext renaming value''
    Domain.Lam bindings type_ plicity closure ->
      Syntax.Lam bindings
        <$> renameValue outerContext renaming type_
        <*> pure plicity
        <*> renameClosure outerContext renaming closure
    Domain.Pi binding type_ plicity closure ->
      Syntax.Pi binding
        <$> renameValue outerContext renaming type_
        <*> pure plicity
        <*> renameClosure outerContext renaming closure
    Domain.Fun domain plicity target ->
      Syntax.Fun
        <$> renameValue outerContext renaming domain
        <*> pure plicity
        <*> renameValue outerContext renaming target

renameClosure
  :: Context v
  -> PartialRenaming v'
  -> Domain.Closure
  -> M (Scope Syntax.Term v')
renameClosure outerContext renaming closure = do
  (env', v) <- Environment.extend $ environment renaming
  closure' <- Evaluation.evaluateClosure closure $ Domain.var v
  renameValue outerContext renaming {environment = env'} closure'

renameSpine
  :: Context v
  -> PartialRenaming v'
  -> Syntax.Term v'
  -> Domain.Spine
  -> M (Syntax.Term v')
renameSpine outerContext renaming head spine =
  case spine of
    Domain.Empty ->
      pure head
    spine' Domain.:> elim -> do
      inner <- renameSpine outerContext renaming head spine'
      renameElimination outerContext renaming inner elim

renameElimination
  :: Context v
  -> PartialRenaming v'
  -> Syntax.Term v'
  -> Domain.Elimination
  -> M (Syntax.Term v')
renameElimination outerContext renaming eliminee elimination =
  case elimination of
    Domain.App plicity arg ->
      Syntax.App eliminee plicity
        <$> renameValue outerContext renaming arg
    Domain.Case (Domain.Branches env' branches defaultBranch) -> do
      branches' <- case branches of
        Syntax.ConstructorBranches constructorTypeName constructorBranches ->
          fmap (Syntax.ConstructorBranches constructorTypeName) $
            OrderedHashMap.forMUnordered constructorBranches $
              mapM $
                renameBranch outerContext renaming env'
        Syntax.LiteralBranches literalBranches ->
          fmap Syntax.LiteralBranches $
            OrderedHashMap.forMUnordered literalBranches $
              mapM \branch -> do
                branch' <- Evaluation.evaluate env' branch
                renameValue outerContext renaming branch'

      defaultBranch' <- forM defaultBranch \branch -> do
        branch' <- Evaluation.evaluate env' branch
        renameValue outerContext renaming branch'
      pure $ Syntax.Case eliminee branches' defaultBranch'

renameBranch
  :: Context outer
  -> PartialRenaming v
  -> Domain.Environment v'
  -> Telescope Bindings Syntax.Type Syntax.Term v'
  -> M (Telescope Bindings Syntax.Type Syntax.Term v)
renameBranch outerContext renaming innerEnv tele =
  case tele of
    Telescope.Empty term -> do
      value <- Evaluation.evaluate innerEnv term
      term' <- renameValue outerContext renaming value
      pure $ Telescope.Empty term'
    Telescope.Extend bindings domain plicity tele' -> do
      domain' <- Evaluation.evaluate innerEnv domain
      domain'' <- renameValue outerContext renaming domain'
      (outerEnv', var) <- Environment.extend $ environment renaming
      let innerEnv' =
            Environment.extendVar innerEnv var
      tele'' <- renameBranch outerContext renaming {environment = outerEnv'} innerEnv' tele'
      pure $ Telescope.Extend bindings domain'' plicity tele''

pruneMeta
  :: Context v
  -> Meta.Index
  -> Seq Bool
  -> M ()
pruneMeta context meta allowedArgs = do
  entry <- Context.lookupMeta context meta
  -- putText $ "pruneMeta " <> show meta
  -- putText $ "pruneMeta " <> show allowedArgs
  case entry of
    Meta.Unsolved metaType _ _ _ -> do
      -- putText $ show metaType
      metaType' <- Evaluation.evaluate Environment.empty metaType
      solution' <- go allowedArgs (Context.emptyFrom context) metaType'
      Context.solveMeta context meta solution'
    Meta.Solved {} ->
      panic "pruneMeta already solved"
    Meta.LazilySolved {} ->
      panic "pruneMeta already solved"
  where
    go :: Seq Bool -> Context v -> Domain.Type -> M (Syntax.Term v)
    go alloweds context' type_ = do
      let renaming =
            PartialRenaming
              { occurs = Nothing
              , environment = Context.toEnvironment context'
              , renamingFlexibility = Flexibility.Rigid
              }
      case alloweds of
        Seq.Empty -> do
          v <- Context.newMeta context' type_
          renameValue context' renaming v
        allowed Seq.:<| alloweds' -> do
          type' <- Context.forceHead context type_
          case type' of
            Domain.Fun domain plicity target -> do
              domain' <- renameValue context' renaming domain
              (context'', _) <-
                if allowed
                  then Context.extend context' "x" domain
                  else do
                    typeMismatch <- lazy $ throwIO $ Error.TypeMismatch mempty
                    Context.extendDef context' "x" (Domain.Lazy typeMismatch) domain
              body <- go alloweds' context'' target
              pure $ Syntax.Lam "x" domain' plicity body
            Domain.Pi binding domain plicity targetClosure -> do
              let name =
                    Binding.toName binding
              (context'', v) <-
                if allowed
                  then Context.extend context' name domain
                  else do
                    typeMismatch <- lazy $ throwIO $ Error.TypeMismatch mempty
                    Context.extendDef context' name (Domain.Lazy typeMismatch) domain
              target <- Evaluation.evaluateClosure targetClosure (Domain.var v)
              domain' <- renameValue context' renaming domain
              body <- go alloweds' context'' target
              pure $ Syntax.Lam (Bindings.Unspanned name) domain' plicity body
            _ -> panic "pruneMeta wrong type"
