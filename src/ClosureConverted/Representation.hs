{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module ClosureConverted.Representation where

import Boxity
import qualified Builtin
import ClosureConverted.Context (Context)
import qualified ClosureConverted.Context as Context
import qualified ClosureConverted.Domain as Domain
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Readback as Readback
import qualified ClosureConverted.Syntax as Syntax
import qualified ClosureConverted.TypeOf as TypeOf
import qualified Core.Syntax
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Monad
import Name (Name)
import qualified Name
import Protolude hiding (empty, force)
import Query (Query)
import qualified Query
import Representation (Representation)
import qualified Representation
import Rock
import Telescope (Telescope)
import qualified Telescope

signature :: Syntax.Definition -> M Representation.Signature
signature def =
  case def of
    Syntax.TypeDeclaration (Syntax.Function tele) -> do
      telescopeSignature context tele mempty $ \context' body parameterRepresentations -> do
        let env' =
              Context.toEnvironment context'
        body' <- Evaluation.evaluate env' body
        returnRepresentation <- typeRepresentation env' body'
        pure $ Representation.FunctionSignature parameterRepresentations returnRepresentation
    Syntax.TypeDeclaration type_ -> do
      type' <- Evaluation.evaluate env type_
      Representation.ConstantSignature <$> typeRepresentation env type'
    Syntax.ConstantDefinition term -> do
      value <- Evaluation.evaluate env term
      type_ <- TypeOf.typeOf context value
      Representation.ConstantSignature <$> typeRepresentation env type_
    Syntax.FunctionDefinition tele ->
      telescopeSignature context tele mempty $ \context' body parameterRepresentations -> do
        let env' =
              Context.toEnvironment context'
        body' <- Evaluation.evaluate env' body
        type_ <- TypeOf.typeOf context' body'
        returnRepresentation <- typeRepresentation env' type_
        pure $ Representation.FunctionSignature parameterRepresentations returnRepresentation
    Syntax.DataDefinition {} ->
      pure $ Representation.ConstantSignature $ Representation.Direct Representation.Doesn'tContainHeapPointers
    Syntax.ParameterisedDataDefinition _boxity tele ->
      telescopeSignature context tele mempty $ \_ _ parameterRepresentations -> do
        pure $ Representation.FunctionSignature parameterRepresentations $ Representation.Direct Representation.Doesn'tContainHeapPointers
  where
    context =
      Context.empty

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
      let env =
            Context.toEnvironment context
      type' <- Evaluation.evaluate env type_
      representation_ <- typeRepresentation env type'
      (context', _var) <- Context.extend context type'
      telescopeSignature context' tele' (representations Tsil.:> representation_) k

type Environment = Environment.Environment Domain.Type

typeRepresentation :: Environment v -> Domain.Type -> M Representation
typeRepresentation env type_ =
  case type_ of
    Domain.Neutral (Domain.Var _) _ ->
      pure $ Representation.Indirect Representation.MightContainHeapPointers
    -- TODO: Handle these special cases in a nicer way
    Domain.Neutral (Domain.Global (Name.Lifted Builtin.TypeName 0)) Tsil.Empty ->
      pure $ Representation.Direct Representation.Doesn'tContainHeapPointers
    Domain.Neutral (Domain.Global (Name.Lifted Builtin.IntName 0)) Tsil.Empty ->
      pure $ Representation.Direct Representation.Doesn'tContainHeapPointers
    Domain.Neutral (Domain.Global global) (Domain.groupSpine -> [Domain.GroupedApps args]) -> do
      globalCase global args
    Domain.Neutral (Domain.Global global) (Domain.groupSpine -> []) -> do
      globalCase global []
    Domain.Neutral {} ->
      pure $ Representation.Indirect Representation.MightContainHeapPointers
    Domain.Con {} ->
      pure $ Representation.Indirect Representation.MightContainHeapPointers
    Domain.Lit {} ->
      pure $ Representation.Indirect Representation.MightContainHeapPointers
    Domain.Glued _ _ type' ->
      typeRepresentation env type'
    Domain.Lazy lazyType -> do
      type' <- force lazyType
      typeRepresentation env type'
    Domain.Pi {} ->
      pure $ Representation.Direct Representation.MightContainHeapPointers
    Domain.Function {} ->
      pure $ Representation.Direct Representation.Doesn'tContainHeapPointers
  where
    globalCase global@(Name.Lifted qualifiedName liftedNameNumber) args = do
      -- TODO caching
      definition <- fetch $ Query.ClosureConverted global
      case definition of
        Syntax.TypeDeclaration _ ->
          pure $ Representation.Indirect Representation.MightContainHeapPointers
        Syntax.ConstantDefinition term -> do
          value <- Evaluation.evaluate Environment.empty term
          type' <- Evaluation.apply env value args
          typeRepresentation env type'
        Syntax.FunctionDefinition tele -> do
          maybeType' <- Evaluation.applyFunction env (Telescope.fromVoid tele) args
          case maybeType' of
            Nothing ->
              pure $ Representation.Direct Representation.MightContainHeapPointers -- a closure
            Just type' ->
              typeRepresentation env type'
        Syntax.DataDefinition Boxed _ ->
          pure $ Representation.Direct Representation.MightContainHeapPointers
        Syntax.DataDefinition Unboxed constructors -> do
          unless (liftedNameNumber == 0) $ panic "ClosureConverted.Representation. Data with name number /= 0"
          unboxedDataRepresentation qualifiedName Environment.empty constructors
        Syntax.ParameterisedDataDefinition Boxed _ ->
          pure $ Representation.Direct Representation.MightContainHeapPointers
        Syntax.ParameterisedDataDefinition Unboxed tele -> do
          unless (liftedNameNumber == 0) $ panic "ClosureConverted.Representation. Data with name number /= 0"
          maybeResult <- Evaluation.applyTelescope env (Telescope.fromVoid tele) args $ unboxedDataRepresentation qualifiedName
          pure $ fromMaybe (Representation.Indirect Representation.MightContainHeapPointers) maybeResult

unboxedDataRepresentation :: Name.Qualified -> Environment v -> Syntax.ConstructorDefinitions v -> M Representation
unboxedDataRepresentation dataTypeName env (Syntax.ConstructorDefinitions constructors) = do
  (_boxity, maybeTags) <- fetch $ Query.ConstructorRepresentations dataTypeName
  fieldRepresentation <-
    Representation.maxM
      [ do
        type' <- Evaluation.evaluate env type_
        constructorFieldRepresentation env type' mempty
      | (_, type_) <- OrderedHashMap.toList constructors
      ]
  pure $ case maybeTags of
    Nothing -> fieldRepresentation
    Just _ -> constructorTagRepresentation <> fieldRepresentation
  where
    constructorTagRepresentation =
      Representation.Direct Representation.Doesn'tContainHeapPointers

constructorFieldRepresentation :: Environment v -> Domain.Type -> Representation -> M Representation
constructorFieldRepresentation env type_ accumulatedRepresentation = do
  type' <- Evaluation.forceHead type_
  case type' of
    Domain.Pi _ fieldType closure -> do
      fieldRepresentation <- typeRepresentation env fieldType
      case accumulatedRepresentation <> fieldRepresentation of
        representation@(Representation.Indirect Representation.MightContainHeapPointers) ->
          pure representation
        accumulatedRepresentation' -> do
          (context', var) <- Environment.extend env
          type'' <- Evaluation.evaluateClosure closure $ Domain.var var
          constructorFieldRepresentation context' type'' accumulatedRepresentation'
    Domain.Neutral {} ->
      pure accumulatedRepresentation
    Domain.Con {} ->
      pure accumulatedRepresentation
    Domain.Lit {} ->
      pure accumulatedRepresentation
    Domain.Glued {} ->
      pure accumulatedRepresentation
    Domain.Lazy {} ->
      pure accumulatedRepresentation
    Domain.Function {} ->
      pure accumulatedRepresentation

-------------------------------------------------------------------------------
compileData :: Environment v -> Name.Qualified -> Syntax.ConstructorDefinitions v -> M (Syntax.Term v)
compileData env dataTypeName (Syntax.ConstructorDefinitions constructors) = do
  (boxity, maybeTags) <- fetch $ Query.ConstructorRepresentations dataTypeName
  case boxity of
    Boxed ->
      pure $ Syntax.Global (Name.Lifted Builtin.WordRepresentationName 0)
    Unboxed -> do
      compiledConstructorFields <- forM (OrderedHashMap.toList constructors) $ \(_, type_) -> do
        type' <- Evaluation.evaluate env type_
        compileUnboxedConstructorFields env type'
      let maxFieldSize =
            foldr
              (\a b -> Syntax.Apply (Name.Lifted Builtin.MaxRepresentationName 0) [a, b])
              (Syntax.Global $ Name.Lifted Builtin.EmptyRepresentationName 0)
              compiledConstructorFields
      pure $ case maybeTags of
        Nothing -> maxFieldSize
        Just _ ->
          Syntax.Apply
            (Name.Lifted Builtin.AddRepresentationName 0)
            [ Syntax.Global (Name.Lifted Builtin.WordRepresentationName 0)
            , maxFieldSize
            ]

compileParameterisedData
  :: Environment v
  -> Name.Qualified
  -> Telescope Name Syntax.Type Syntax.ConstructorDefinitions v
  -> M (Telescope Name Syntax.Type Syntax.Term v)
compileParameterisedData env dataTypeName tele =
  case tele of
    Telescope.Empty constructors ->
      Telescope.Empty <$> compileData env dataTypeName constructors
    Telescope.Extend name type_ plicity tele' -> do
      (env', _) <- Environment.extend env
      Telescope.Extend name type_ plicity <$> compileParameterisedData env' dataTypeName tele'

compileUnboxedConstructorFields :: Environment v -> Domain.Type -> M (Syntax.Term v)
compileUnboxedConstructorFields env type_ = do
  type' <- Evaluation.forceHead type_
  case type' of
    Domain.Pi _name fieldType closure -> do
      fieldType' <- Readback.readback env fieldType
      value <- Domain.Lazy <$> lazy (panic "unboxed data representation depends on field") -- TODO real error
      rest <- Evaluation.evaluateClosure closure value
      rest' <- compileUnboxedConstructorFields env rest
      pure $ Syntax.Apply (Name.Lifted Builtin.AddRepresentationName 0) [fieldType', rest']
    Domain.Neutral {} ->
      empty
    Domain.Con {} ->
      empty
    Domain.Lit {} ->
      empty
    Domain.Glued {} ->
      empty
    Domain.Lazy {} ->
      empty
    Domain.Function {} ->
      empty
  where
    empty =
      pure $ Syntax.Global (Name.Lifted Builtin.EmptyRepresentationName 0)

compileBoxedConstructorFields :: Environment v -> Domain.Type -> [Domain.Value] -> M (Syntax.Term v)
compileBoxedConstructorFields env type_ args = do
  type' <- Evaluation.forceHead type_
  case (type', args) of
    (Domain.Pi _name fieldType closure, arg : args') -> do
      fieldType' <- Readback.readback env fieldType
      rest <- Evaluation.evaluateClosure closure arg
      rest' <- compileBoxedConstructorFields env rest args'
      pure $ Syntax.Apply (Name.Lifted Builtin.AddRepresentationName 0) [fieldType', rest']
    (Domain.Pi {}, []) ->
      panic "compileBoxedConstructorFields: constructor type field mismatch"
    (Domain.Neutral {}, []) ->
      empty
    (Domain.Con {}, []) ->
      empty
    (Domain.Lit {}, []) ->
      empty
    (Domain.Glued {}, []) ->
      empty
    (Domain.Lazy {}, []) ->
      empty
    (Domain.Function {}, []) ->
      empty
    (_, _ : _) ->
      panic "compileBoxedConstructorFields: constructor type field mismatch"
  where
    empty =
      pure $ Syntax.Global (Name.Lifted Builtin.EmptyRepresentationName 0)

-------------------------------------------------------------------------------
data Branches v
  = LiteralBranches (Syntax.LiteralBranches v)
  | UntaggedConstructorBranch !Boxity (Telescope Name Syntax.Type Syntax.Term v)
  | TaggedConstructorBranches !Boxity [(Int, Telescope Name Syntax.Type Syntax.Term v)]
  deriving (Eq, Show)

compileBranches :: MonadFetch Query m => Syntax.Branches v -> m (Branches v)
compileBranches branches =
  case branches of
    Syntax.LiteralBranches literalBranches ->
      pure $ LiteralBranches literalBranches
    Syntax.ConstructorBranches typeName constructorBranches -> do
      (boxity, maybeTags) <- fetch $ Query.ConstructorRepresentations typeName
      pure $ case (maybeTags, OrderedHashMap.toList constructorBranches) of
        (Nothing, [(_, constructorBranch)]) -> UntaggedConstructorBranch boxity constructorBranch
        (Nothing, _) -> panic "ClosureConverted.Representation.compileBranches: Untagged constructor branch length mismatch"
        (Just tags, constructorBranchesList) ->
          TaggedConstructorBranches
            boxity
            [(tags HashMap.! constructor, branch) | (constructor, branch) <- constructorBranchesList]

constructorRepresentations :: Name.Qualified -> Task Query (Boxity, Maybe (HashMap Name.Constructor Int))
constructorRepresentations name = do
  (definition, _) <- fetch $ Query.ElaboratedDefinition name
  pure $ case definition of
    Core.Syntax.DataDefinition boxity tele ->
      ( boxity
      , Telescope.under tele $ \(Core.Syntax.ConstructorDefinitions constructors) ->
          case OrderedHashMap.toList constructors of
            [] -> Nothing
            [_] -> Nothing
            constructorList ->
              Just $
                HashMap.fromList [(constructor, tag) | (tag, (constructor, _)) <- zip [0 ..] constructorList]
      )
    _ ->
      panic "ClosureConverted.Representation.compileConstructors: No data definition"
