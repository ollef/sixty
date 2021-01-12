{-# language ViewPatterns #-}
{-# language RankNTypes #-}
module ClosureConverted.Representation where

import Boxity
import qualified Builtin
import ClosureConverted.Context (Context)
import qualified ClosureConverted.Context as Context
import qualified ClosureConverted.Domain as Domain
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Syntax as Syntax
import qualified ClosureConverted.TypeOf as TypeOf
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Monad
import qualified Name
import Name (Name)
import Protolude hiding (force)
import qualified Query
import Representation (Representation)
import qualified Representation
import Rock
import qualified Scope
import Telescope (Telescope)
import qualified Telescope

signature :: Name.Lifted -> Syntax.Definition -> M (Maybe Representation.Signature)
signature (Name.Lifted name _) def = 
  case def of
    Syntax.TypeDeclaration _ ->
      pure Nothing

    Syntax.ConstantDefinition term -> do
      value <- Evaluation.evaluate env term
      type_ <- TypeOf.typeOf context value
      Just . Representation.ConstantSignature <$> representation env type_

    Syntax.FunctionDefinition tele ->
      telescopeSignature context tele mempty $ \context' body parameterRepresentations -> do
        let
          env' =
            Context.toEnvironment context'
        body' <- Evaluation.evaluate env' body
        type_ <- TypeOf.typeOf context' body'
        returnRepresentation <- representation env' type_
        pure $ Just $ Representation.FunctionSignature parameterRepresentations returnRepresentation

    Syntax.DataDefinition Unboxed constructorDefinitions ->
      Just . Representation.ConstantSignature <$> unboxedDataRepresentation env constructorDefinitions

    Syntax.DataDefinition Boxed _ ->
      pure $ Just $ Representation.ConstantSignature Representation.Direct

    Syntax.ParameterisedDataDefinition Unboxed tele ->
      telescopeSignature context tele mempty $ \context' constructorDefinitions parameterRepresentations -> do
        returnRepresentation <- unboxedDataRepresentation (Context.toEnvironment context') constructorDefinitions
        pure $ Just $ Representation.FunctionSignature parameterRepresentations returnRepresentation

    Syntax.ParameterisedDataDefinition Boxed tele ->
      telescopeSignature context tele mempty $ \_ _ parameterRepresentations ->
        pure $ Just $ Representation.FunctionSignature parameterRepresentations Representation.Direct

  where
    context =
      Context.empty $ Scope.KeyedName Scope.Definition name

    env =
      Context.toEnvironment context

telescopeSignature
  :: Context v
  -> Telescope Name Syntax.Type body v
  -> Tsil Representation
  -> (forall v'. Context v' -> body v' -> [Representation] -> M result)
  -> M result
telescopeSignature context tele representations k =
  case tele of
    Telescope.Empty body ->
      k context body $ toList representations

    Telescope.Extend _name type_ _plicity tele' -> do
      let
        env =
          Context.toEnvironment context
      type' <- Evaluation.evaluate env type_
      representation_ <- representation env type'
      (context', _var) <- Context.extend context type'
      telescopeSignature context' tele' (representations Tsil.:> representation_) k

type Environment = Environment.Environment Domain.Type

representation :: Environment v -> Domain.Type -> M Representation
representation env type_ =
  case type_ of
    Domain.Neutral (Domain.Var _) _ ->
      pure Representation.Indirect

    -- TODO: Handle these special cases in a nicer way
    Domain.Neutral (Domain.Global (Name.Lifted Builtin.TypeName 0)) Tsil.Empty ->
      pure Representation.Direct

    Domain.Neutral (Domain.Global (Name.Lifted Builtin.IntName 0)) Tsil.Empty ->
      pure Representation.Direct

    Domain.Neutral (Domain.Global global) (Domain.groupSpine -> [Domain.GroupedApps args]) -> do
      -- TODO caching
      maybeDefinition <- fetch $ Query.ClosureConverted global
      case maybeDefinition of
        Nothing ->
          pure Representation.Indirect

        Just definition ->
          case definition of
            Syntax.TypeDeclaration _ ->
              pure Representation.Indirect

            Syntax.ConstantDefinition term -> do
              value <- Evaluation.evaluate (Environment.emptyFrom env) term
              type' <- Evaluation.apply env value args
              representation env type'

            Syntax.FunctionDefinition tele -> do
              maybeType' <- Evaluation.applyFunction env (Telescope.fromVoid tele) args
              case maybeType' of
                Nothing ->
                  pure Representation.Direct -- a closure

                Just type' ->
                  representation env type'

            Syntax.DataDefinition Boxed _ ->
              pure Representation.Direct

            Syntax.DataDefinition Unboxed constructors ->
              unboxedDataRepresentation (Environment.emptyFrom env) constructors

            Syntax.ParameterisedDataDefinition Boxed _ ->
              pure Representation.Direct

            Syntax.ParameterisedDataDefinition Unboxed tele -> do
              maybeResult <- Evaluation.applyTelescope env (Telescope.fromVoid tele) args unboxedDataRepresentation
              pure $ fromMaybe Representation.Indirect maybeResult

    Domain.Neutral {} ->
      pure Representation.Indirect

    Domain.Con {} ->
      pure Representation.Indirect

    Domain.Lit {} ->
      pure Representation.Indirect

    Domain.Glued _ _ type' -> do
      type'' <- force type'
      representation env type''

    Domain.Pi {} ->
      pure Representation.Direct

    Domain.Function {} ->
      pure Representation.Direct

unboxedDataRepresentation :: Environment v -> Syntax.ConstructorDefinitions v -> M Representation
unboxedDataRepresentation env (Syntax.ConstructorDefinitions constructors) = do
  let
    constructorsList =
      OrderedHashMap.toList constructors
  fieldRepresentation <- Representation.maxM
    [ do
      type' <- Evaluation.evaluate env type_
      constructorFieldRepresentation env type' mempty
    | (_, type_) <- constructorsList
    ]
  pure $ case (constructorsList, fieldRepresentation) of
    ([], _) ->
      Representation.Empty

    ([_], _) ->
      fieldRepresentation

    (_, Representation.Empty) ->
      Representation.Direct

    _ ->
      Representation.Indirect

constructorFieldRepresentation :: Environment v -> Domain.Type -> Representation -> M Representation
constructorFieldRepresentation env type_ accumulatedRepresentation = do
  type' <- Evaluation.forceHead type_
  case type' of
    Domain.Pi _ fieldType closure -> do
      fieldRepresentation <- representation env fieldType
      case accumulatedRepresentation <> fieldRepresentation of
        Representation.Indirect ->
          pure Representation.Indirect

        accumulatedRepresentation' -> do
          (context', var) <- Environment.extend env
          type'' <- Evaluation.evaluateClosure closure $ Domain.var var
          constructorFieldRepresentation context' type'' accumulatedRepresentation'

    Domain.Neutral {} ->
      pure Representation.Empty

    Domain.Con {} ->
      pure Representation.Empty

    Domain.Lit {} ->
      pure Representation.Empty

    Domain.Glued {} ->
      pure Representation.Empty

    Domain.Function {} ->
      pure Representation.Empty
