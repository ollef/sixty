{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
module ClosureConverted.TypeOf where

import Protolude hiding (head, typeOf)

import Rock

import qualified Builtin
import ClosureConverted.Context (Context)
import qualified ClosureConverted.Context as Context
import qualified ClosureConverted.Domain as Domain
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Readback as Readback
import qualified ClosureConverted.Syntax as Syntax
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Environment
import qualified Literal
import Monad
import Name (Name)
import qualified Name
import qualified Query
import Telescope (Telescope)
import qualified Telescope

typeOfDefinition :: Context Void -> Syntax.Definition -> M (Syntax.Type Void)
typeOfDefinition context definition = do
  let
    env =
      Context.toEnvironment context
  typeValue <-
    case definition of
      Syntax.TypeDeclaration type_ ->
        Evaluation.evaluate env type_

      Syntax.ConstantDefinition term -> do
        value <- Evaluation.evaluate env term
        typeOf context value

      Syntax.FunctionDefinition tele ->
        Domain.Function <$> typeOfFunction context tele

      Syntax.DataDefinition _ _ ->
        pure $ Domain.global $ Name.Lifted Builtin.TypeName 0

      Syntax.ParameterisedDataDefinition _ tele ->
        Evaluation.evaluate env $
          Telescope.fold
            (\name domain _ -> Syntax.Pi name domain)
            (Telescope.hoist (const $ Syntax.Global $ Name.Lifted Builtin.TypeName 0) tele)

  Readback.readback (Context.toEnvironment context) typeValue

typeOfFunction
  :: Context v
  -> Telescope Name Syntax.Type Syntax.Term v
  -> M (Telescope Name Syntax.Type Syntax.Type v)
typeOfFunction context tele =
  case tele of
    Telescope.Empty body -> do
      let
        env =
          Context.toEnvironment context
      body' <- Evaluation.evaluate env body
      bodyType <- typeOf context body'
      bodyType' <- Readback.readback env bodyType
      pure $ Telescope.Empty bodyType'

    Telescope.Extend binding domain plicity target -> do
      domain' <- Evaluation.evaluate (Context.toEnvironment context) domain
      (context', _) <- Context.extend context domain'
      target' <- typeOfFunction context' target
      pure $ Telescope.Extend binding domain plicity target'


typeOf :: Context v -> Domain.Value -> M Domain.Type
typeOf context value =
  case value of
    Domain.Neutral head spine -> do
      headType <- typeOfHead context head
      typeOfSpineApplication context headType spine

    Domain.Con con params args -> do
      conType <- fetch $ Query.ClosureConvertedConstructorType con
      conType' <-
        Evaluation.evaluate (Context.toEnvironment context) $
          Telescope.fold
            (\name domain _ -> Syntax.Pi name domain)
            (Telescope.fromVoid conType)
      typeOfApplications conType' $ params <> args

    Domain.Lit lit ->
      case lit of
        Literal.Integer _ ->
          pure $ Domain.global $ Name.Lifted Builtin.IntName 0

    Domain.Glued hd spine _ ->
      typeOf context $ Domain.Neutral hd spine

    Domain.Pi {} ->
      pure $ Domain.global $ Name.Lifted Builtin.TypeName 0

    Domain.Function {} ->
      pure $ Domain.global $ Name.Lifted Builtin.TypeName 0

typeOfHead
  :: Context v
  -> Domain.Head
  -> M Domain.Type
typeOfHead context head =
  case head of
    Domain.Var var ->
      pure $ Context.lookupVarType var context

    Domain.Global global -> do
      type_ <- fetch $ Query.ClosureConvertedType global
      type' <- Evaluation.evaluate (Context.toEnvironment context) $ Syntax.fromVoid type_
      case type' of
        Domain.Function tele ->
          Evaluation.evaluate (Context.toEnvironment context) $
            Telescope.fold
              (\name domain _ -> Syntax.Pi name domain)
              (Telescope.fromVoid tele)

        _ ->
          pure type'

typeOfSpineApplication
  :: Foldable f
  => Context v
  -> Domain.Type
  -> f Domain.Elimination
  -> M Domain.Type
typeOfSpineApplication =
  foldlM . typeOfElimination

typeOfElimination :: Context v -> Domain.Type -> Domain.Elimination -> M Domain.Type
typeOfElimination context type_ elimination =
  case elimination of
    Domain.App arg ->
      typeOfApplication type_ arg

    Domain.Case (Domain.Branches env branches defaultBranch) ->
      case defaultBranch of
        Just term -> do
          value' <- Evaluation.evaluate env term
          typeOf context value'

        Nothing ->
          case branches of
            Syntax.ConstructorBranches _ constructorBranches ->
              case OrderedHashMap.elems constructorBranches of
                branchTele:_ ->
                  typeOfTelescope context env branchTele

                [] ->
                  panic "TODO closure converted type of branchless case"

            Syntax.LiteralBranches literalBranches ->
              case OrderedHashMap.elems literalBranches of
                body:_ -> do
                  body' <- Evaluation.evaluate env body
                  typeOf context body'

                [] ->
                  panic "TODO closure converted type of branchless case"


typeOfApplication
  :: Domain.Type
  -> Domain.Value
  -> M Domain.Type
typeOfApplication type_ arg =
  case type_ of
    Domain.Pi _ _ closure ->
      Evaluation.evaluateClosure closure arg

    _ ->
      panic "ClosureConverted.TypeOf.typeOfApplication: non-function"

typeOfApplications
  :: Domain.Type
  -> [Domain.Value]
  -> M Domain.Type
typeOfApplications =
  foldlM typeOfApplication

typeOfTelescope
  :: Context v'
  -> Domain.Environment v
  -> Telescope Name Syntax.Type Syntax.Term v
  -> M Domain.Type
typeOfTelescope context env tele =
  case tele of
    Telescope.Empty branch -> do
      branch' <- Evaluation.evaluate env branch
      typeOf context branch'

    Telescope.Extend _ type_ _ tele' -> do
      type' <- Evaluation.evaluate env type_
      (context', var) <- Context.extend context type'
      typeOfTelescope context' (Environment.extendVar env var) tele'
