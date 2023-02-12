{-# LANGUAGE FlexibleContexts #-}

module ClosureConversion where

import qualified ClosureConverted.Syntax as ClosureConverted
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified LambdaLifted.Syntax as LambdaLifted
import Name (Name)
import qualified Name
import Protolude
import Query (Query)
import qualified Query
import Rock
import Telescope (Telescope)
import qualified Telescope

convertDefinition
  :: MonadFetch Query m
  => LambdaLifted.Definition
  -> m ClosureConverted.Definition
convertDefinition def =
  case def of
    LambdaLifted.TypeDeclaration type_ ->
      ClosureConverted.TypeDeclaration <$> convertTypeDeclaration type_
    LambdaLifted.ConstantDefinition (Telescope.Empty term) ->
      ClosureConverted.ConstantDefinition <$> convertTerm term
    LambdaLifted.ConstantDefinition tele ->
      ClosureConverted.FunctionDefinition <$> convertTelescope tele
    LambdaLifted.DataDefinition boxity (Telescope.Empty (LambdaLifted.ConstructorDefinitions constrDefs)) ->
      ClosureConverted.DataDefinition boxity . ClosureConverted.ConstructorDefinitions
        <$> OrderedHashMap.mapMUnordered convertTerm constrDefs
    LambdaLifted.DataDefinition boxity tele ->
      ClosureConverted.ParameterisedDataDefinition boxity <$> convertParameterisedDataDefinition tele

convertParameterisedDataDefinition
  :: MonadFetch Query m
  => Telescope Name LambdaLifted.Type LambdaLifted.ConstructorDefinitions v
  -> m (Telescope Name ClosureConverted.Type ClosureConverted.ConstructorDefinitions v)
convertParameterisedDataDefinition tele =
  case tele of
    Telescope.Empty (LambdaLifted.ConstructorDefinitions constrDefs) ->
      Telescope.Empty . ClosureConverted.ConstructorDefinitions <$> OrderedHashMap.mapMUnordered convertTerm constrDefs
    Telescope.Extend binding type_ plicity tele' ->
      Telescope.Extend binding
        <$> convertTerm type_
        <*> pure plicity
        <*> convertParameterisedDataDefinition tele'

convertTerm
  :: MonadFetch Query m
  => LambdaLifted.Term v
  -> m (ClosureConverted.Term v)
convertTerm term =
  convertAppliedTerm term []

convertAppliedTerm
  :: MonadFetch Query m
  => LambdaLifted.Term v
  -> [ClosureConverted.Term v]
  -> m (ClosureConverted.Term v)
convertAppliedTerm term args =
  case term of
    LambdaLifted.Var var ->
      applyArgs args $
        pure $
          ClosureConverted.Var var
    LambdaLifted.Global global ->
      convertGlobal global args
    LambdaLifted.Con con conParams conArgs ->
      ClosureConverted.Con con <$> mapM convertTerm conParams <*> mapM convertTerm conArgs
    LambdaLifted.Lit lit ->
      pure $ ClosureConverted.Lit lit
    LambdaLifted.Let binding term' type_ body ->
      applyArgs args $
        ClosureConverted.Let binding
          <$> convertTerm term'
          <*> convertTerm type_
          <*> convertTerm body
    LambdaLifted.Pi binding domain target ->
      ClosureConverted.Pi binding
        <$> convertTerm domain
        <*> convertTerm target
    LambdaLifted.App fun arg -> do
      arg' <- convertTerm arg
      convertAppliedTerm fun $ arg' : args
    LambdaLifted.Case scrutinee branches defaultBranch ->
      applyArgs args $
        ClosureConverted.Case
          <$> convertTerm scrutinee
          <*> convertBranches branches
          <*> mapM convertTerm defaultBranch

convertGlobal
  :: MonadFetch Query m
  => Name.Lifted
  -> [ClosureConverted.Term v]
  -> m (ClosureConverted.Term v)
convertGlobal global args = do
  definition <- fetch $ Query.LambdaLiftedDefinition global
  let nonFunctionCase =
        applyArgs args $ pure $ ClosureConverted.Global global

      functionCase tele =
        pure $
          case (Telescope.length tele, length args) of
            (arity, numArgs)
              | arity == numArgs ->
                  ClosureConverted.Apply global args
              | arity < numArgs -> do
                  let (preArgs, postArgs) =
                        splitAt arity args

                  ClosureConverted.ApplyClosure
                    (ClosureConverted.Apply global preArgs)
                    postArgs
              | otherwise ->
                  ClosureConverted.Closure global args

  case definition of
    LambdaLifted.TypeDeclaration type_ ->
      case LambdaLifted.pisView identity type_ of
        Telescope.Empty {} ->
          nonFunctionCase
        tele@Telescope.Extend {} ->
          functionCase tele
    LambdaLifted.ConstantDefinition (Telescope.Empty _) ->
      nonFunctionCase
    LambdaLifted.DataDefinition _ (Telescope.Empty _) ->
      nonFunctionCase
    LambdaLifted.ConstantDefinition tele ->
      functionCase tele
    LambdaLifted.DataDefinition _ tele ->
      functionCase tele

convertTypeDeclaration :: MonadFetch Query m => LambdaLifted.Type Void -> m (ClosureConverted.Type Void)
convertTypeDeclaration type_ =
  case LambdaLifted.pisView identity type_ of
    Telescope.Empty _ ->
      convertTerm type_
    tele@Telescope.Extend {} ->
      ClosureConverted.Function <$> Telescope.hoistA convertTerm convertTerm tele

convertBranches
  :: MonadFetch Query m
  => LambdaLifted.Branches v
  -> m (ClosureConverted.Branches v)
convertBranches branches =
  case branches of
    LambdaLifted.ConstructorBranches constructorTypeName constructorBranches ->
      ClosureConverted.ConstructorBranches constructorTypeName
        <$> OrderedHashMap.mapMUnordered convertTelescope constructorBranches
    LambdaLifted.LiteralBranches literalBranches ->
      ClosureConverted.LiteralBranches
        <$> OrderedHashMap.mapMUnordered convertTerm literalBranches

convertTelescope
  :: MonadFetch Query m
  => Telescope Name LambdaLifted.Type LambdaLifted.Term v
  -> m (Telescope Name ClosureConverted.Type ClosureConverted.Term v)
convertTelescope tele =
  case tele of
    Telescope.Empty term ->
      Telescope.Empty <$> convertTerm term
    Telescope.Extend binding type_ plicity tele' ->
      Telescope.Extend binding
        <$> convertTerm type_
        <*> pure plicity
        <*> convertTelescope tele'

applyArgs
  :: Monad m
  => [ClosureConverted.Term v]
  -> m (ClosureConverted.Term v)
  -> m (ClosureConverted.Term v)
applyArgs args mresult =
  case args of
    [] ->
      mresult
    _ -> do
      result <- mresult
      pure $ ClosureConverted.ApplyClosure result args
