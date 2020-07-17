{-# language OverloadedStrings #-}
module Evaluation where

import Protolude hiding (Seq, head, force, evaluate)

import Rock

import Binding (Binding)
import Bindings (Bindings)
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Tsil as Tsil
import qualified Core.Domain as Domain
import qualified Domain.Telescope as Domain (Telescope)
import qualified Domain.Telescope
import qualified Environment
import Literal (Literal)
import Monad
import qualified Name
import Plicity
import qualified Query
import qualified Core.Syntax as Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

evaluateConstructorDefinitions
  :: Domain.Environment v
  -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
  -> M (Domain.Telescope Binding Domain.Type (OrderedHashMap Name.Constructor Domain.Type))
evaluateConstructorDefinitions env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrs) -> do
      constrs' <- OrderedHashMap.forMUnordered constrs $ evaluate env
      pure $ Domain.Telescope.Empty constrs'

    Telescope.Extend binding domain plicity target -> do
      domain' <- evaluate env domain
      pure $ Domain.Telescope.Extend binding domain' plicity $ \param -> do
        (env', _) <- Environment.extendValue env param
        evaluateConstructorDefinitions env' target

evaluate :: Domain.Environment v -> Syntax.Term v -> M Domain.Value
evaluate env term =
  case term of
    Syntax.Var index -> do
      let
        var =
          Environment.lookupIndexVar index env

      pure $
        case Environment.lookupVarValue var env of
          Nothing ->
            Domain.var var

          Just value ->
            Domain.Glued (Domain.Var var) mempty $ eager value

    Syntax.Global name -> do
      definitionVisible <- fetch $ Query.IsDefinitionVisible (Environment.scopeKey env) name
      if definitionVisible then do
        maybeDefinition <- fetch $ Query.ElaboratedDefinition name
        case maybeDefinition of
          Just (Syntax.ConstantDefinition term', _) -> do
            value <- lazy $ evaluate (Environment.emptyFrom env) term'
            pure $ Domain.Glued (Domain.Global name) mempty value

          _ ->
            pure $ Domain.global name

      else
        pure $ Domain.global name

    Syntax.Con con ->
      pure $ Domain.con con

    Syntax.Lit lit ->
      pure $ Domain.Lit lit

    Syntax.Meta meta ->
      pure $ Domain.meta meta

    Syntax.Let _ term' _ body -> do
      term'' <- evaluate env term'
      (env', _) <- Environment.extendValue env term''
      evaluate env' body

    Syntax.Pi binding domain plicity target -> do
      domain' <- evaluate env domain
      pure $ Domain.Pi binding domain' plicity (Domain.Closure env target)

    Syntax.Fun domain plicity target -> do
      domain' <- evaluate env domain
      target' <- evaluate env target
      pure $ Domain.Fun domain' plicity target'

    Syntax.Lam binding type_ plicity body -> do
      type' <- evaluate env type_
      pure $ Domain.Lam binding type' plicity (Domain.Closure env body)

    Syntax.App fun plicity arg -> do
      fun' <- evaluate env fun
      arg' <- evaluate env arg
      apply fun' plicity arg'

    Syntax.Case scrutinee branches defaultBranch -> do
      scrutineeValue <- evaluate env scrutinee
      case (scrutineeValue, branches) of
        (Domain.Con constr args, Syntax.ConstructorBranches _ constructorBranches) ->
          chooseConstructorBranch env constr (toList args) constructorBranches defaultBranch

        (Domain.Lit lit, Syntax.LiteralBranches literalBranches) ->
          chooseLiteralBranch env lit literalBranches defaultBranch

        _ ->
          pure $
            Domain.Neutral
            (Domain.Case scrutineeValue $ Domain.Branches env branches defaultBranch)
            mempty

    Syntax.Spanned _ term' ->
      evaluate env term'

chooseConstructorBranch
  :: Domain.Environment v
  -> Name.QualifiedConstructor
  -> [(Plicity, Domain.Value)]
  -> Syntax.ConstructorBranches v
  -> Maybe (Syntax.Term v)
  -> M Domain.Value
chooseConstructorBranch outerEnv qualifiedConstr@(Name.QualifiedConstructor _ constr) outerArgs branches defaultBranch =
  case (OrderedHashMap.lookup constr branches, defaultBranch) of
    (Nothing, Nothing) ->
      panic "chooseBranch no branches"

    (Nothing, Just branch) ->
      evaluate outerEnv branch

    (Just (_, tele), _) -> do
      constrTypeTele <- fetch $ Query.ConstructorType qualifiedConstr
      go outerEnv (dropTypeArgs constrTypeTele outerArgs) tele
  where
    dropTypeArgs
      :: Telescope n t t' v
      -> [(Plicity, value)]
      -> [(Plicity, value)]
    dropTypeArgs tele args =
      case (tele, args) of
        (Telescope.Empty _, _) ->
          args

        (Telescope.Extend _ _ plicity1 tele', (plicity2, _):args')
          | plicity1 == plicity2 ->
            dropTypeArgs tele' args'

        _ ->
          panic "chooseBranch arg mismatch"

    go
      :: Domain.Environment v
      -> [(Plicity, Domain.Value)]
      -> Telescope Bindings Syntax.Type Syntax.Term v
      -> M Domain.Value
    go env args tele =
      case (args, tele) of
        ([], Telescope.Empty branch) ->
          evaluate env branch

        ((plicity1, arg):args', Telescope.Extend _ _ plicity2 target)
          | plicity1 == plicity2 -> do
            (env', _) <- Environment.extendValue env arg
            go env' args' target

          | otherwise ->
            panic $ "chooseConstructorBranch mismatch " <> show (plicity1, plicity2)

        _ ->
          panic "chooseConstructorBranch mismatch"

chooseLiteralBranch
  :: Domain.Environment v
  -> Literal
  -> Syntax.LiteralBranches v
  -> Maybe (Syntax.Term v)
  -> M Domain.Value
chooseLiteralBranch outerEnv lit branches defaultBranch =
  case (OrderedHashMap.lookup lit branches, defaultBranch) of
    (Nothing, Nothing) ->
      panic "chooseLiteralBranch no branches"

    (Nothing, Just branch) ->
      evaluate outerEnv branch

    (Just (_, branch), _) ->
      evaluate outerEnv branch

apply :: Domain.Value -> Plicity -> Domain.Value -> M Domain.Value
apply fun plicity arg =
  case fun of
    Domain.Lam _ _  plicity' closure
      | plicity == plicity' ->
      evaluateClosure closure arg

    Domain.Neutral hd args ->
      pure $ Domain.Neutral hd (args Tsil.:> (plicity, arg))

    Domain.Glued hd args value -> do
      appliedValue <- lazy $ do
        value' <- force value
        apply value' plicity arg
      pure $ Domain.Glued hd (args Tsil.:> (plicity, arg)) appliedValue


    Domain.Con con args ->
      pure $ Domain.Con con $ args Tsil.:> (plicity, arg)

    _ ->
      panic "applying non-function"

applySpine :: Domain.Value -> Domain.Spine -> M Domain.Value
applySpine =
  foldM (\val (plicity, arg) -> apply val plicity arg)

evaluateClosure :: Domain.Closure -> Domain.Value -> M Domain.Value
evaluateClosure (Domain.Closure env body) argument = do
  (env', _) <- Environment.extendValue env argument
  evaluate env' body

-- | Evaluate the head of a value further, if possible
-- due to new value bindings. Also evalutes through glued values.
forceHead
  :: Domain.Environment v
  -> Domain.Value
  -> M Domain.Value
forceHead env value =
  case value of
    Domain.Neutral (Domain.Var var) spine
      | Just headValue <- Environment.lookupVarValue var env -> do
        value' <- applySpine headValue spine
        forceHead env value'

    Domain.Neutral (Domain.Case scrutinee branches@(Domain.Branches branchEnv brs defaultBranch)) spine -> do
      scrutinee' <- forceHead env scrutinee
      case (scrutinee', brs) of
        (Domain.Con constr constructorArgs, Syntax.ConstructorBranches _ constructorBranches) -> do
          value' <- chooseConstructorBranch branchEnv constr (toList constructorArgs) constructorBranches defaultBranch
          value'' <- forceHead env value'
          applySpine value'' spine

        (Domain.Lit lit, Syntax.LiteralBranches literalBranches) -> do
          value' <- chooseLiteralBranch branchEnv lit literalBranches defaultBranch
          value'' <- forceHead env value'
          applySpine value'' spine

        _ ->
          pure $ Domain.Neutral (Domain.Case scrutinee' branches) spine

    Domain.Glued _ _ value' -> do
      value'' <- force value'
      forceHead env value''

    _ ->
      pure value
