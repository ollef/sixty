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
          domain <-
            Evaluation.evaluateClosure
              domainClosure
              (Domain.var var)
          explicitFunCase context' name var source domain

      Domain.Fun source domain
        | HashMap.null implicits -> do
          (context', var) <- Context.extendUnnamed context "x" source
          explicitFunCase context' "x" var source domain

      Domain.Pi name source Implicit domainClosure -> do
        (context', var) <- Context.extendUnnamed context name source
        let
          value =
            Domain.var var
        domain <- Evaluation.evaluateClosure domainClosure value
        source'' <- Elaboration.readback context source
        body <- check context' (shiftImplicit name value source <$> clauses) domain
        pure $ Syntax.Lam name source'' Implicit body

      _ -> do
        (term', type_) <- infer context clauses
        f <- Unification.tryUnify context type_ expectedType
        pure $ f term'
  where
    implicits =
      foldMap clauseImplicits clauses

    explicitFunCase context' name var source domain = do
      source'' <- Elaboration.readback context source
      clauses' <- mapM (shiftExplicit context (Domain.var var) source) clauses
      body <- check context' clauses' domain
      pure $ Syntax.Lam name source'' Explicit body

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
        (context', var) <- Context.extendUnnamed context "x" source
        clauses' <- mapM (shiftExplicit context (Domain.var var) source) clauses
        (body, domain) <- infer context' clauses'
        domain' <- Elaboration.readback context' domain

        pure
          ( Syntax.Lam "x" source' Explicit body
          , Domain.Pi "x" source Explicit
            $ Domain.Closure (Context.toEnvironment context) domain'
          )

      [(name, _)] -> do
        source <- Context.newMetaType context
        source' <- Elaboration.readback context source
        (context', var) <- Context.extendUnnamed context name source
        let
          value =
            Domain.var var
        (body, domain) <- infer context' (shiftImplicit name value source <$> clauses)
        domain' <- Elaboration.readback context' domain

        pure
          ( Syntax.Lam name source' Implicit body
          , Domain.Pi name source Implicit
            $ Domain.Closure (Context.toEnvironment context) domain'
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
    Presyntax.ImplicitPattern _ namedPats:patterns'
      | HashMap.null namedPats ->
        removeEmptyImplicits $ Clause (Presyntax.Clause span patterns' term) matches

    _ ->
      clause

clauseImplicits :: Clause -> HashMap Name Presyntax.Pattern
clauseImplicits (Clause (Presyntax.Clause _ patterns _) _) =
  case patterns of
    Presyntax.ImplicitPattern _ namedPats:_ ->
      namedPats

    _ ->
      mempty

shiftImplicit :: Name -> Domain.Value -> Domain.Type -> Clause -> Clause
shiftImplicit name value type_ (Clause (Presyntax.Clause span patterns term) matches) =
  case patterns of
    Presyntax.ImplicitPattern patSpan namedPats:patterns'
      | HashMap.member name namedPats ->
        Clause
          (Presyntax.Clause
            span
            (Presyntax.ImplicitPattern patSpan (HashMap.delete name namedPats):patterns')
            term
          )
          (matches Tsil.:> Matching.Match value Implicit (namedPats HashMap.! name) type_)

    _ ->
      Clause
        (Presyntax.Clause span patterns term)
        (matches Tsil.:> Matching.Match value Implicit (Presyntax.Pattern span Presyntax.WildcardPattern) type_)

shiftExplicit :: Context v -> Domain.Value -> Domain.Type -> Clause -> M Clause
shiftExplicit context value type_ clause@(Clause (Presyntax.Clause span patterns term) matches) =
  case patterns of
    Presyntax.ExplicitPattern pat:patterns' ->
      pure $
        Clause
          (Presyntax.Clause span patterns' term)
          (matches Tsil.:> Matching.Match value Explicit pat type_)

    Presyntax.ImplicitPattern patSpan _:patterns' -> do
      Context.report
        (Context.spanned patSpan context)
        (Error.PlicityMismatch Error.Argument $ Error.Mismatch Explicit Implicit)
      shiftExplicit
        context
        value
        type_
        (Clause
          (Presyntax.Clause span patterns' term)
          matches
        )

    [] -> do
      Context.report
        (Context.spanned span context)
        (Error.PlicityMismatch Error.Argument $ Error.Missing Explicit)
      pure clause
