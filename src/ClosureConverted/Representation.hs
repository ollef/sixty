{-# LANGUAGE BlockArguments #-}
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
import Low.PassBy (PassBy)
import qualified Low.PassBy as PassBy
import qualified Low.Representation as Representation
import qualified Low.Syntax as Low
import Monad
import Name (Name)
import qualified Name
import Protolude hiding (empty, force, repr)
import Query (Query)
import qualified Query
import Rock
import Telescope (Telescope)
import qualified Telescope

signature :: Syntax.Definition -> M Low.Signature
signature def =
  case def of
    Syntax.TypeDeclaration (Syntax.Function tele) -> do
      telescopeSignature context tele mempty \context' body passParametersBy -> do
        let env' = Context.toEnvironment context'
        body' <- Evaluation.evaluate env' body
        passReturnBy <- passTypeBy env' body'
        pure $ Low.FunctionSignature (functionOperand <$> passParametersBy) $ functionOperand passReturnBy
    Syntax.TypeDeclaration type_ -> do
      type' <- Evaluation.evaluate env type_
      passBy <- passTypeBy env type'
      case passBy of
        PassBy.Value repr ->
          pure $ Low.ConstantSignature repr
        PassBy.Reference -> panic "couldn't determine representation of type declaration" -- TODO real error?
    Syntax.ConstantDefinition term -> do
      value <- Evaluation.evaluate env term
      type_ <- TypeOf.typeOf context value
      passBy <- passTypeBy env type_
      case passBy of
        PassBy.Value repr ->
          pure $ Low.ConstantSignature repr
        PassBy.Reference -> panic "couldn't determine representation of constant definition" -- TODO real error?
    Syntax.FunctionDefinition tele ->
      telescopeSignature context tele mempty \context' body passParametersBy -> do
        let env' = Context.toEnvironment context'
        body' <- Evaluation.evaluate env' body
        type_ <- TypeOf.typeOf context' body'
        passReturnBy <- passTypeBy env' type_
        pure $ Low.FunctionSignature (functionOperand <$> passParametersBy) $ functionOperand passReturnBy
    Syntax.DataDefinition {} ->
      pure $ Low.ConstantSignature Representation.type_
    Syntax.ParameterisedDataDefinition _boxity tele ->
      telescopeSignature context tele mempty \_ _ passParametersBy -> do
        pure $ Low.FunctionSignature (functionOperand <$> passParametersBy) $ functionOperand $ PassBy.Value Representation.type_
  where
    functionOperand passBy@(PassBy.Value repr)
      | Representation.shouldPassByReference repr = PassBy.Reference
      | otherwise = passBy
    functionOperand PassBy.Reference = PassBy.Reference

    context = Context.empty
    env = Context.toEnvironment context

telescopeSignature
  :: Context v
  -> Telescope Name Syntax.Type body v
  -> Tsil PassBy
  -> (forall v'. Context v' -> body v' -> [PassBy] -> M result)
  -> M result
telescopeSignature context tele passBys k =
  case tele of
    Telescope.Empty body ->
      k context body $ toList passBys
    Telescope.Extend _name type_ _plicity tele' -> do
      let env = Context.toEnvironment context
      type' <- Evaluation.evaluate env type_
      passBy <- passTypeBy env type'
      (context', _var) <- Context.extend context type'
      telescopeSignature context' tele' (passBys Tsil.:> passBy) k

type Environment = Environment.Environment Domain.Type

passTypeBy :: Environment v -> Domain.Type -> M PassBy
passTypeBy env type_ =
  case type_ of
    Domain.Neutral (Domain.Var _) _ ->
      pure PassBy.Reference
    -- TODO: Handle these special cases in a nicer way
    Domain.Neutral (Domain.Global (Name.Lifted Builtin.TypeName 0)) Tsil.Empty ->
      pure $ PassBy.Value Representation.type_
    Domain.Neutral (Domain.Global (Name.Lifted Builtin.IntName 0)) Tsil.Empty ->
      pure $ PassBy.Value Representation.int
    Domain.Neutral (Domain.Global global) (Domain.groupSpine -> [Domain.GroupedApps args]) -> do
      globalCase global args
    Domain.Neutral (Domain.Global global) (Domain.groupSpine -> []) -> do
      globalCase global []
    Domain.Neutral {} ->
      pure PassBy.Reference
    Domain.Con {} ->
      pure PassBy.Reference
    Domain.Lit {} ->
      pure PassBy.Reference
    Domain.Glued _ _ type' ->
      passTypeBy env type'
    Domain.Lazy lazyType -> do
      type' <- force lazyType
      passTypeBy env type'
    Domain.Pi {} ->
      pure $ PassBy.Value Representation.pointer
    Domain.Function {} ->
      pure $ PassBy.Value Representation.rawFunctionPointer
  where
    globalCase global@(Name.Lifted qualifiedName liftedNameNumber) args = do
      -- TODO caching
      definition <- fetch $ Query.ClosureConverted global
      case definition of
        Syntax.TypeDeclaration _ ->
          pure PassBy.Reference
        Syntax.ConstantDefinition term -> do
          value <- Evaluation.evaluate Environment.empty term
          type' <- Evaluation.apply env value args
          passTypeBy env type'
        Syntax.FunctionDefinition tele -> do
          maybeType' <- Evaluation.applyFunction env (Telescope.fromZero tele) args
          case maybeType' of
            Nothing ->
              pure $ PassBy.Value Representation.pointer -- a closure
            Just type' ->
              passTypeBy env type'
        Syntax.DataDefinition Boxed _ ->
          pure $ PassBy.Value Representation.pointer
        Syntax.DataDefinition Unboxed constructors -> do
          unless (liftedNameNumber == 0) $ panic "ClosureConverted.Representation. Data with name number /= 0"
          passUnboxedDataBy qualifiedName Environment.empty constructors
        Syntax.ParameterisedDataDefinition Boxed _ ->
          pure $ PassBy.Value Representation.pointer
        Syntax.ParameterisedDataDefinition Unboxed tele -> do
          unless (liftedNameNumber == 0) $ panic "ClosureConverted.Representation. Data with name number /= 0"
          maybeResult <- Evaluation.applyTelescope env (Telescope.fromZero tele) args $ passUnboxedDataBy qualifiedName
          pure $ fromMaybe PassBy.Reference maybeResult

maxM :: (Monad m) => [m PassBy] -> m PassBy
maxM = go mempty
  where
    go repr [] = pure $ PassBy.Value repr
    go repr (m : ms) = do
      passBy <- m
      case passBy of
        PassBy.Reference -> pure passBy
        PassBy.Value repr' -> go (Representation.leastUpperBound repr repr') ms

passProductBy :: PassBy -> PassBy -> PassBy
passProductBy (PassBy.Value repr1) (PassBy.Value repr2) = PassBy.Value $ repr1 <> repr2
passProductBy PassBy.Reference _ = PassBy.Reference
passProductBy _ PassBy.Reference = PassBy.Reference

passUnboxedDataBy :: Name.Qualified -> Environment v -> Syntax.ConstructorDefinitions v -> M PassBy
passUnboxedDataBy dataTypeName env (Syntax.ConstructorDefinitions constructors) = do
  (_boxity, maybeTags) <- fetch $ Query.ConstructorRepresentations dataTypeName
  passFieldsBy <-
    maxM
      [ do
        type' <- Evaluation.evaluate env type_
        passConstructorFieldsBy env type' $ PassBy.Value mempty
      | (_, type_) <- OrderedHashMap.toList constructors
      ]
  pure case maybeTags of
    Nothing -> passFieldsBy
    Just _ -> passProductBy passConstructorTagBy passFieldsBy
      where
        passConstructorTagBy =
          PassBy.Value Representation.int

passConstructorFieldsBy :: Environment v -> Domain.Type -> PassBy -> M PassBy
passConstructorFieldsBy env type_ accumulatedPassBy = do
  type' <- Evaluation.forceHead type_
  case type' of
    Domain.Pi _ fieldType closure -> do
      passFieldBy <- passTypeBy env fieldType
      case passProductBy accumulatedPassBy passFieldBy of
        PassBy.Reference ->
          pure PassBy.Reference
        accumulatedPassBy' -> do
          (context', var) <- Environment.extend env
          type'' <- Evaluation.evaluateClosure closure $ Domain.var var
          passConstructorFieldsBy context' type'' accumulatedPassBy'
    Domain.Neutral {} ->
      pure accumulatedPassBy
    Domain.Con {} ->
      pure accumulatedPassBy
    Domain.Lit {} ->
      pure accumulatedPassBy
    Domain.Glued {} ->
      pure accumulatedPassBy
    Domain.Lazy {} ->
      pure accumulatedPassBy
    Domain.Function {} ->
      pure accumulatedPassBy

-------------------------------------------------------------------------------
compileData :: Environment v -> Name.Qualified -> Syntax.ConstructorDefinitions v -> M (Syntax.Term v)
compileData env dataTypeName (Syntax.ConstructorDefinitions constructors) = do
  (boxity, maybeTags) <- fetch $ Query.ConstructorRepresentations dataTypeName
  case boxity of
    Boxed ->
      pure $ Syntax.Global (Name.Lifted Builtin.PointerRepresentationName 0)
    Unboxed -> do
      compiledConstructorFields <- forM (OrderedHashMap.toList constructors) \(_, type_) -> do
        type' <- Evaluation.evaluate env type_
        compileUnboxedConstructorFields env type'
      let maxFieldSize =
            foldr
              (\a b -> Syntax.Apply (Name.Lifted Builtin.MaxRepresentationName 0) [a, b])
              (Syntax.Global $ Name.Lifted Builtin.EmptyRepresentationName 0)
              compiledConstructorFields
      pure case maybeTags of
        Nothing -> maxFieldSize
        Just _ ->
          Syntax.Apply
            (Name.Lifted Builtin.AddRepresentationName 0)
            [ Syntax.Global (Name.Lifted Builtin.IntName 0)
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
    (Domain.Neutral {}, []) -> empty
    (Domain.Con {}, []) -> empty
    (Domain.Lit {}, []) -> empty
    (Domain.Glued {}, []) -> empty
    (Domain.Lazy {}, []) -> empty
    (Domain.Function {}, []) -> empty
    (_, _ : _) ->
      panic "compileBoxedConstructorFields: constructor type field mismatch"
  where
    empty = pure $ Syntax.Global (Name.Lifted Builtin.EmptyRepresentationName 0)

-------------------------------------------------------------------------------
data Branches v
  = LiteralBranches (Syntax.LiteralBranches v)
  | UntaggedConstructorBranch !Boxity (Telescope Name Syntax.Type Syntax.Term v)
  | TaggedConstructorBranches !Boxity [(Name.QualifiedConstructor, Telescope Name Syntax.Type Syntax.Term v)]
  deriving (Eq, Show)

compileBranches :: (MonadFetch Query m) => Syntax.Branches v -> m (Branches v)
compileBranches branches =
  case branches of
    Syntax.LiteralBranches literalBranches -> pure $ LiteralBranches literalBranches
    Syntax.ConstructorBranches typeName constructorBranches -> do
      (boxity, maybeTags) <- fetch $ Query.ConstructorRepresentations typeName
      pure case (maybeTags, OrderedHashMap.toList constructorBranches) of
        (Nothing, [(_, constructorBranch)]) -> UntaggedConstructorBranch boxity constructorBranch
        (Nothing, _) -> panic "ClosureConverted.Representation.compileBranches: Untagged constructor branch length mismatch"
        (Just _tags, constructorBranchesList) ->
          TaggedConstructorBranches
            boxity
            [(Name.QualifiedConstructor typeName constructor, branch) | (constructor, branch) <- constructorBranchesList]

constructorRepresentations :: Name.Qualified -> Task Query (Boxity, Maybe (HashMap Name.Constructor Int))
constructorRepresentations name = do
  (definition, _) <- fetch $ Query.ElaboratedDefinition name
  pure case definition of
    Core.Syntax.DataDefinition boxity tele ->
      ( boxity
      , Telescope.under tele \(Core.Syntax.ConstructorDefinitions constructors) ->
          case OrderedHashMap.toList constructors of
            [] -> Nothing
            [_] -> Nothing
            constructorList ->
              Just $
                HashMap.fromList [(constructor, tag) | (tag, (constructor, _)) <- zip [0 ..] constructorList]
      )
    _ ->
      panic "ClosureConverted.Representation.compileConstructors: No data definition"
