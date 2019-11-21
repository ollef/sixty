{-# language OverloadedStrings #-}
module TypeOf where

import Protolude

import qualified Data.HashMap.Lazy as HashMap
import Rock

import qualified Builtin
import Context (Context)
import qualified Context
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Binding
import qualified Elaboration
import qualified Environment
import qualified Evaluation
import qualified Meta
import Monad
import qualified Query
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

typeOf :: Context v -> Domain.Value -> M Domain.Type
typeOf context value =
  case value of
    Domain.Neutral hd spine -> do
      headType <- typeOfHead context hd
      typeOfApplication context headType spine

    Domain.Glued hd spine _ ->
      typeOf context $ Domain.Neutral hd spine

    Domain.Lam name type_ plicity closure -> do
      (context', var) <- Context.extendUnnamed context name type_
      body <- Evaluation.evaluateClosure closure (Domain.var var)
      bodyType <- typeOf context' body
      bodyType' <- Elaboration.readback context' bodyType
      pure $
        Domain.Pi name type_ plicity $
        Domain.Closure (Context.toEnvironment context) bodyType'

    Domain.Pi {} ->
      pure Builtin.Type

    Domain.Fun {} ->
      pure Builtin.Type

    Domain.Case _ (Domain.Branches env branches defaultBranch) ->
      case defaultBranch of
        Just term -> do
          value' <- Evaluation.evaluate env term
          typeOf context value'

        Nothing ->
          case HashMap.toList branches of
            (_, (_, branchTele)):_ ->
              typeOfBranch context env branchTele

            [] ->
              panic "TODO type of branchless case"

typeOfHead :: Context v -> Domain.Head -> M Domain.Type
typeOfHead context hd =
  case hd of
    Domain.Var var ->
      pure $ Context.lookupVarType var context

    Domain.Global global -> do
      type_ <- fetch $ Query.ElaboratedType global
      Evaluation.evaluate (Environment.empty $ Context.scopeKey context) type_

    Domain.Con constr -> do
      tele <- fetch $ Query.ConstructorType constr
      let
        type_ =
          Telescope.fold Syntax.Pi tele
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

typeOfApplication :: Context v -> Domain.Type -> Domain.Spine -> M Domain.Type
typeOfApplication context type_ spine = do
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

typeOfBranch
  :: Context v'
  -> Domain.Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> M Domain.Type
typeOfBranch context env tele =
  case tele of
    Telescope.Empty branch -> do
      branch' <- Evaluation.evaluate env branch
      typeOf context branch'

    Telescope.Extend binding type_ _ tele' -> do
      type' <- Evaluation.evaluate env type_
      (context', var) <- Context.extendUnnamed context (Binding.toName binding) type'
      typeOfBranch context' (Environment.extendVar env var) tele'
