{-# language DuplicateRecordFields #-}
{-# language ViewPatterns #-}
{-# language OverloadedStrings #-}
module Elaboration.Clauses where

import Protolude hiding (check, force)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import {-# SOURCE #-} qualified Elaboration
import Context (Context)
import qualified Context
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Elaboration.Matching as Matching
import qualified Error
import qualified Evaluation
import Monad
import Name (Name)
import Plicity
import qualified Presyntax
import qualified Syntax
import qualified Unification

check
  :: Context v
  -> [Clause]
  -> Domain.Type
  -> M (Syntax.Term v)
check context (fmap removeEmptyImplicits -> clauses) expectedType
  | all isEmpty clauses = do
    let
      matchingClauses =
        [ Matching.Clause
          { _span = span
          , _matches = toList matches
          , _rhs = rhs
          }
        | Clause (Presyntax.Clause span _ rhs) matches <- clauses
        ]
    Matching.elaborateClauses context matchingClauses expectedType

  | otherwise = do
    expectedType' <- Context.forceHead context expectedType
    case expectedType' of
      Domain.Pi name source Explicit domainClosure
        | HashMap.null implicits -> do
          (context', var) <- Context.extendUnnamed context name source
          let
            value =
              Domain.var var
          source' <- force source
          source'' <- Elaboration.readback context source'
          domain <-
            Evaluation.evaluateClosure
              domainClosure
              (Lazy $ pure $ Domain.var var)
          body <- check context' (shiftExplicit value source' <$> clauses) domain
          pure $ Syntax.Lam name source'' Explicit body

      Domain.Fun source domain
        | HashMap.null implicits -> do
          (context', var) <- Context.extendUnnamed context "x" source
          let
            value =
              Domain.var var
          source' <- force source
          source'' <- Elaboration.readback context source'
          domain' <- force domain
          body <- check context' (shiftExplicit value source' <$> clauses) domain'
          pure $ Syntax.Lam "x" source'' Explicit body

      Domain.Pi name source Implicit domainClosure -> do
        (context', var) <- Context.extendUnnamed context name source
        let
          value =
            Domain.var var
        domain <- Evaluation.evaluateClosure domainClosure $ Lazy $ pure value
        source' <- force source
        source'' <- Elaboration.readback context source'
        body <- check context' (shiftImplicit name value source' <$> clauses) domain
        pure $ Syntax.Lam name source'' Implicit body

      _ -> do
        (term', type_) <- infer context clauses
        f <- Unification.tryUnify context type_ expectedType'
        pure $ f term'
  where
    implicits =
      foldMap clauseImplicits clauses

infer
  :: Context v
  -> [Clause]
  -> M (Syntax.Term v, Domain.Type)
infer context (fmap removeEmptyImplicits -> clauses)
  | all isEmpty clauses = do
    let
      matchingClauses =
        [ Matching.Clause
          { _span = span
          , _matches = toList matches
          , _rhs = rhs
          }
        | Clause (Presyntax.Clause span _ rhs) matches <- clauses
        ]
    expectedType <- Context.newMetaType context
    result <- Matching.elaborateClauses context matchingClauses expectedType
    pure (result, expectedType)

  | otherwise =
    case HashMap.toList implicits of
      [] -> do
        source <- Context.newMetaType context
        source' <- Elaboration.readback context source
        (context', var) <- Context.extendUnnamed context "x" $ Lazy $ pure source
        let
          value =
            Domain.var var
        (body, domain) <- infer context' (shiftExplicit value source <$> clauses)
        domain' <- Elaboration.readback context' domain

        pure
          ( Syntax.Lam "x" source' Explicit body
          , Domain.Pi "x" (Lazy $ pure source) Explicit
            $ Domain.Closure (Context.toEvaluationEnvironment context) domain'
          )

      [(name, _)] -> do
        source <- Context.newMetaType context
        source' <- Elaboration.readback context source
        (context', var) <- Context.extendUnnamed context name $ Lazy $ pure source
        let
          value =
            Domain.var var
        (body, domain) <- infer context' (shiftImplicit name value source <$> clauses)
        domain' <- Elaboration.readback context' domain

        pure
          ( Syntax.Lam name source' Implicit body
          , Domain.Pi name (Lazy $ pure source) Implicit
            $ Domain.Closure (Context.toEvaluationEnvironment context) domain'
          )

      _ -> do
        Context.report context Error.UnableToInferImplicitLambda
        Elaboration.inferenceFailed context
  where
    implicits =
      foldMap clauseImplicits clauses

-------------------------------------------------------------------------------

data Clause = Clause !Presyntax.Clause (Tsil Matching.Match)

isEmpty :: Clause -> Bool
isEmpty (Clause (Presyntax.Clause _ patterns _) _) =
  case patterns of
    [] ->
      True

    _:_ ->
      False

removeEmptyImplicits :: Clause -> Clause
removeEmptyImplicits clause@(Clause (Presyntax.Clause span patterns term) matches) =
  case patterns of
    Presyntax.ImplicitPattern namedPats:patterns'
      | HashMap.null namedPats ->
        removeEmptyImplicits $ Clause (Presyntax.Clause span patterns' term) matches

    _ ->
      clause

clauseImplicits :: Clause -> HashMap Name Presyntax.Pattern
clauseImplicits (Clause (Presyntax.Clause _ patterns _) _) =
  case patterns of
    Presyntax.ImplicitPattern namedPats:_ ->
      namedPats

    _ ->
      mempty

shiftImplicit :: Name -> Domain.Value -> Domain.Type -> Clause -> Clause
shiftImplicit name value type_ (Clause (Presyntax.Clause span patterns term) matches) =
  case patterns of
    Presyntax.ImplicitPattern namedPats:patterns'
      | HashMap.member name namedPats ->
        Clause
          (Presyntax.Clause
            span
            (Presyntax.ImplicitPattern (HashMap.delete name namedPats):patterns')
            term
          )
          (matches Tsil.:> Matching.Match value Implicit (namedPats HashMap.! name) type_)

    _ ->
      Clause
        (Presyntax.Clause span patterns term)
        (matches Tsil.:> Matching.Match value Implicit (Presyntax.Pattern span Presyntax.WildcardPattern) type_)

shiftExplicit :: Domain.Value -> Domain.Type -> Clause -> Clause
shiftExplicit value type_ (Clause (Presyntax.Clause span patterns term) matches) =
  case patterns of
    Presyntax.ExplicitPattern pat:patterns' ->
      Clause
        (Presyntax.Clause span patterns' term)
        (matches Tsil.:> Matching.Match value Explicit pat type_)

    _ ->
      panic "TODO error message"
