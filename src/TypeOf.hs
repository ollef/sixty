{-# language OverloadedStrings #-}
module TypeOf where

import Protolude hiding (typeOf)

import Rock

import qualified Binding
import Bindings (Bindings)
import qualified Bindings
import qualified Builtin
import Context (Context)
import qualified Context
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Tsil as Tsil
import qualified Core.Domain as Domain
import qualified Elaboration
import qualified Environment
import qualified Evaluation
import qualified Meta
import Monad
import qualified Query
import qualified Core.Syntax as Syntax
import Telescope (Telescope)
import qualified Telescope

typeOf :: Context v -> Domain.Value -> M Domain.Type
typeOf context value =
  case value of
    Domain.Neutral hd spine -> do
      headType <- typeOfHead context hd
      typeOfApplication context headType spine

    Domain.Lit lit ->
      pure $ Elaboration.inferLiteral lit

    Domain.Con constr args -> do
      tele <- fetch $ Query.ConstructorType constr
      let
        type_ =
          Telescope.fold Syntax.Pi tele
      constrType <- Evaluation.evaluate (Environment.empty $ Context.scopeKey context) type_
      typeOfApplication context constrType args

    Domain.Glued hd spine _ ->
      typeOf context $ Domain.Neutral hd spine

    Domain.Lam bindings type_ plicity closure -> do
      let
        name =
          Bindings.toName bindings
      (context', var) <- Context.extend context name type_
      body <- Evaluation.evaluateClosure closure (Domain.var var)
      bodyType <- typeOf context' body
      bodyType' <- Elaboration.readback context' bodyType
      pure $
        Domain.Pi (Binding.Unspanned name) type_ plicity $
        Domain.Closure (Context.toEnvironment context) bodyType'

    Domain.Pi {} ->
      pure Builtin.Type

    Domain.Fun {} ->
      pure Builtin.Type

typeOfHead :: Context v -> Domain.Head -> M Domain.Type
typeOfHead context hd =
  case hd of
    Domain.Var var ->
      pure $ Context.lookupVarType var context

    Domain.Global global -> do
      type_ <- fetch $ Query.ElaboratedType global
      Evaluation.evaluate (Environment.empty $ Context.scopeKey context) type_

    Domain.Meta index -> do
      solution <- Context.lookupMeta index context
      let
        type_ =
          case solution of
            Meta.Unsolved type' _ ->
              type'

            Meta.Solved _ type' ->
              type'

      Evaluation.evaluate (Environment.empty $ Context.scopeKey context) type_

    Domain.Case _ (Domain.Branches env branches defaultBranch) ->
      case defaultBranch of
        Just term -> do
          value' <- Evaluation.evaluate env term
          typeOf context value'

        Nothing ->
          case branches of
            Syntax.ConstructorBranches _ constructorBranches ->
              case OrderedHashMap.elems constructorBranches of
                (_, branchTele):_ ->
                  typeOfTelescope context env branchTele

                [] ->
                  panic "TODO type of branchless case"

            Syntax.LiteralBranches literalBranches ->
              case OrderedHashMap.elems literalBranches of
                (_, body):_ -> do
                  body' <- Evaluation.evaluate env body
                  typeOf context body'

                [] ->
                  panic "TODO type of branchless case"

typeOfApplication :: Context v -> Domain.Type -> Domain.Spine -> M Domain.Type
typeOfApplication context type_ spine =
  case spine of
    Tsil.Empty ->
      pure type_

    spine' Tsil.:> (plicity, arg) -> do
      type' <- typeOfApplication context type_ spine'
      type'' <- Context.forceHead context type'
      case type'' of
        Domain.Fun _ plicity' target
          | plicity == plicity' ->
            pure target

        Domain.Pi _ _ plicity' targetClosure
          | plicity == plicity' ->
            Evaluation.evaluateClosure targetClosure arg

        _ ->
          panic "typeOfApplication: type or plicity mismatch"

typeOfTelescope
  :: Context v'
  -> Domain.Environment v
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> M Domain.Type
typeOfTelescope context env tele =
  case tele of
    Telescope.Empty branch -> do
      branch' <- Evaluation.evaluate env branch
      typeOf context branch'

    Telescope.Extend bindings type_ _ tele' -> do
      type' <- Evaluation.evaluate env type_
      (context', var) <- Context.extend context (Bindings.toName bindings) type'
      typeOfTelescope context' (Environment.extendVar env var) tele'
