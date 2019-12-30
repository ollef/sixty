{-# language FlexibleContexts #-}
module ClosureConvert where

import Protolude
import Rock

import qualified ClosureConverted.Syntax as ClosureConverted
import qualified LambdaLifted.Syntax as LambdaLifted
import Query (Query)
import qualified Query
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

convertDefinition
  :: MonadFetch Query m
  => LambdaLifted.Definition
  -> m ClosureConverted.Definition
convertDefinition def =
  case def of
    LambdaLifted.ConstantDefinition (Telescope.Empty term) ->
      ClosureConverted.ConstantDefinition <$> convertTerm term

    LambdaLifted.ConstantDefinition tele ->
      ClosureConverted.FunctionDefinition <$> convertTelescope tele

    LambdaLifted.DataDefinition (Telescope.Empty (LambdaLifted.ConstructorDefinitions constrDefs)) ->
      ClosureConverted.DataDefinition . ClosureConverted.ConstructorDefinitions <$>
        mapM convertTerm constrDefs

    LambdaLifted.DataDefinition tele ->
      ClosureConverted.ParameterisedDataDefinition <$> convertParameterisedDataDefinition tele

convertParameterisedDataDefinition
  :: MonadFetch Query m
  => Telescope LambdaLifted.Type LambdaLifted.ConstructorDefinitions v
  -> m (Telescope ClosureConverted.Type ClosureConverted.ConstructorDefinitions v)
convertParameterisedDataDefinition tele =
  case tele of
    Telescope.Empty (LambdaLifted.ConstructorDefinitions constrDefs) ->
      Telescope.Empty . ClosureConverted.ConstructorDefinitions <$> mapM convertTerm constrDefs

    Telescope.Extend binding type_ plicity tele' ->
      Telescope.Extend binding <$>
        convertTerm type_ <*>
        pure plicity <*>
        convertParameterisedDataDefinition tele'

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
      applyArgs $
        pure $ ClosureConverted.Var var

    LambdaLifted.Global global -> do
      maybeDef <- fetch $ Query.LambdaLifted global
      let
        nonFunctionCase =
          applyArgs $ pure $ ClosureConverted.Global global

        functionCase tele =
          pure $
            case (Telescope.length tele, length args) of
              (arity, numArgs)
                | arity == numArgs ->
                  ClosureConverted.Apply global args

                | arity < numArgs -> do
                  let
                    (preArgs, postArgs) =
                      splitAt arity args

                  ClosureConverted.ApplyClosure
                    (ClosureConverted.Apply global preArgs)
                    postArgs

                | otherwise ->
                  ClosureConverted.Closure global args

      case maybeDef of
        Just (LambdaLifted.ConstantDefinition (Telescope.Empty _)) ->
          nonFunctionCase

        Just (LambdaLifted.DataDefinition (Telescope.Empty _)) ->
          nonFunctionCase

        Just (LambdaLifted.ConstantDefinition tele) ->
          functionCase tele

        Just (LambdaLifted.DataDefinition tele) ->
          functionCase tele

        Nothing ->
          nonFunctionCase

    LambdaLifted.Con con conArgs ->
      ClosureConverted.Con con <$> mapM convertTerm conArgs

    LambdaLifted.Lit lit ->
      pure $ ClosureConverted.Lit lit

    LambdaLifted.Let binding term' type_ body ->
      applyArgs $
        ClosureConverted.Let binding <$>
          convertTerm term' <*>
          convertTerm type_ <*>
          convertTerm body

    LambdaLifted.Pi binding domain target ->
      ClosureConverted.Pi binding <$>
        convertTerm domain <*>
        convertTerm target

    LambdaLifted.App fun arg -> do
      arg' <- convertTerm arg
      convertAppliedTerm fun $ arg' : args

    LambdaLifted.Case scrutinee branches defaultBranch ->
      applyArgs $
        ClosureConverted.Case <$>
          convertTerm scrutinee <*>
          convertBranches branches <*>
          mapM convertTerm defaultBranch

  where
    applyArgs mresult =
      case args of
        [] ->
          mresult

        _ -> do
          result <- mresult
          pure $ ClosureConverted.ApplyClosure result args

convertBranches
  :: MonadFetch Query m
  => LambdaLifted.Branches v
  -> m (ClosureConverted.Branches v)
convertBranches branches =
  case branches of
    LambdaLifted.ConstructorBranches constructorBranches ->
      ClosureConverted.ConstructorBranches <$>
        mapM convertTelescope constructorBranches

    LambdaLifted.LiteralBranches literalBranches ->
      ClosureConverted.LiteralBranches <$>
        mapM convertTerm literalBranches

convertTelescope
  :: MonadFetch Query m
  => Telescope LambdaLifted.Type LambdaLifted.Term v
  -> m (Telescope ClosureConverted.Type ClosureConverted.Term v)
convertTelescope tele =
  case tele of
    Telescope.Empty term ->
      Telescope.Empty <$> convertTerm term

    Telescope.Extend binding type_ plicity tele' ->
      Telescope.Extend binding <$>
        convertTerm type_ <*>
        pure plicity <*>
        convertTelescope tele'
