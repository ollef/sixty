{-# language OverloadedStrings #-}
module Core.Evaluation where

import Protolude hiding (Seq, head, force, evaluate)

import Rock

import Core.Binding (Binding)
import Core.Bindings (Bindings)
import qualified Core.Domain as Domain
import qualified Core.Domain.Telescope as Domain (Telescope)
import qualified Core.Domain.Telescope as Domain.Telescope
import qualified Core.Syntax as Syntax
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Tsil as Tsil
import qualified Environment
import qualified Index
import Literal (Literal)
import Monad
import qualified Name
import Plicity
import qualified Query
import Telescope (Telescope)
import qualified Telescope

evaluateConstructorDefinitions
  :: Domain.Environment v
  -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
  -> M (Domain.Telescope (OrderedHashMap Name.Constructor Domain.Type))
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

          Just value
            | Index.succ index > Environment.glueableBefore env ->
              Domain.Glued (Domain.Var var) mempty value

            | otherwise ->
              value

    Syntax.Global name -> do
      definitionVisible <- fetch $ Query.IsDefinitionVisible (Environment.scopeKey env) name
      if definitionVisible then do
        maybeDefinition <- fetch $ Query.ElaboratedDefinition name
        case maybeDefinition of
          Just (Syntax.ConstantDefinition term', _) -> do
            value <- lazy $ evaluate (Environment.emptyFrom env) term'
            pure $ Domain.Glued (Domain.Global name) mempty $ Domain.Lazy value

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

    Syntax.PostponedCheck _ term' ->
      evaluate env term'

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
      case_ scrutineeValue $ Domain.Branches env branches defaultBranch

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

      | otherwise ->
        panic "Core.Evaluation: plicity mismatch"

    Domain.Neutral hd spine ->
      pure $ Domain.Neutral hd $ spine Domain.:> Domain.App plicity arg

    Domain.Glued hd spine value -> do
      appliedValue <- apply value plicity arg
      pure $ Domain.Glued hd (spine Domain.:> Domain.App plicity arg) appliedValue

    Domain.Lazy lazyValue -> do
      lazyValue' <- lazy $ do
        value' <- force lazyValue
        apply value' plicity arg
      pure $ Domain.Lazy lazyValue'

    Domain.Con con args ->
      pure $ Domain.Con con $ args Tsil.:> (plicity, arg)

    _ ->
      panic "applying non-function"

case_ :: Domain.Value -> Domain.Branches -> M Domain.Value
case_ scrutinee branches@(Domain.Branches env branches' defaultBranch) =
  case (scrutinee, branches') of
    (Domain.Con constr args, Syntax.ConstructorBranches _ constructorBranches) ->
      chooseConstructorBranch env constr (toList args) constructorBranches defaultBranch

    (Domain.Lit lit, Syntax.LiteralBranches literalBranches) ->
      chooseLiteralBranch env lit literalBranches defaultBranch

    (Domain.Neutral head spine, _) ->
      pure $ Domain.Neutral head $ spine Domain.:> Domain.Case branches

    (Domain.Glued hd spine value, _) -> do
      casedValue <- case_ value branches
      pure $ Domain.Glued hd (spine Domain.:> Domain.Case branches) casedValue

    (Domain.Lazy lazyValue, _) -> do
      lazyValue' <- lazy $ do
        value' <- force lazyValue
        case_ value' branches
      pure $ Domain.Lazy lazyValue'

    _ ->
      panic "casing non-constructor"

applyElimination :: Domain.Value -> Domain.Elimination -> M Domain.Value
applyElimination value elimination =
  case elimination of
    Domain.App plicity arg ->
      apply value plicity arg

    Domain.Case branches ->
      case_ value branches

applySpine :: Domain.Value -> Domain.Spine -> M Domain.Value
applySpine =
  Domain.foldlM applyElimination

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

    Domain.Glued _ _ value' -> do
      forceHead env value'

    Domain.Lazy lazyValue -> do
      value' <- force lazyValue
      forceHead env value'

    _ ->
      pure value
