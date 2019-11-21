{-# language DuplicateRecordFields #-}
{-# language ViewPatterns #-}
{-# language OverloadedStrings #-}
module Elaboration.Clauses where

import Protolude hiding (check, force)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import {-# SOURCE #-} qualified Elaboration
import Binding (Binding)
import qualified Binding
import Context (Context)
import qualified Context
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Elaboration.Matching as Matching
import qualified Elaboration.Matching.SuggestedName as SuggestedName
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
      Domain.Pi name domain Explicit targetClosure
        | HashMap.null implicits -> do
          (context', var) <- Context.extendUnnamed context name domain
          target <-
            Evaluation.evaluateClosure
              targetClosure
              (Domain.var var)
          explicitFunCase context' (Binding.Unspanned name) var domain target

      Domain.Fun domain Explicit target
        | HashMap.null implicits -> do
          binding <- nextExplicitBinding context clauses
          (context', var) <- Context.extendUnnamed context (Binding.toName binding) domain
          explicitFunCase context' binding var domain target

      Domain.Pi piName domain Implicit targetClosure -> do
        binding <- nextImplicitBinding context piName clauses
        (context', var) <- Context.extendUnnamed context (Binding.toName binding) domain
        let
          value =
            Domain.var var
        target <- Evaluation.evaluateClosure targetClosure value
        domain'' <- Elaboration.readback context domain
        body <- check context' (shiftImplicit (Binding.toName binding) value domain <$> clauses) target
        pure $ Syntax.Lam binding domain'' Implicit body

      _ -> do
        (term', type_) <- infer context clauses
        f <- Unification.tryUnify context type_ expectedType
        pure $ f term'
  where
    implicits =
      foldMap clauseImplicits clauses

    explicitFunCase context' binding var domain target = do
      domain'' <- Elaboration.readback context domain
      clauses' <- mapM (shiftExplicit context (Domain.var var) domain) clauses
      body <- check context' clauses' target
      pure $ Syntax.Lam binding domain'' Explicit body

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
        domain <- Context.newMetaType context
        domain' <- Elaboration.readback context domain
        binding <- nextExplicitBinding context clauses
        let
          name =
            Binding.toName binding
        (context', var) <- Context.extendUnnamed context name domain
        clauses' <- mapM (shiftExplicit context (Domain.var var) domain) clauses
        (body, target) <- infer context' clauses'
        target' <- Elaboration.readback context' target

        pure
          ( Syntax.Lam binding domain' Explicit body
          , Domain.Pi name domain Explicit
            $ Domain.Closure (Context.toEnvironment context) target'
          )

      [(piName, _)] -> do
        binding <- nextImplicitBinding context piName clauses
        let
          name =
            Binding.toName binding
        domain <- Context.newMetaType context
        domain' <- Elaboration.readback context domain
        (context', var) <- Context.extendUnnamed context name domain
        let
          value =
            Domain.var var
        (body, target) <- infer context' (shiftImplicit name value domain <$> clauses)
        target' <- Elaboration.readback context' target

        pure
          ( Syntax.Lam binding domain' Implicit body
          , Domain.Pi name domain Implicit
            $ Domain.Closure (Context.toEnvironment context) target'
          )

      _ -> do
        Context.report context Error.UnableToInferImplicitLambda
        Elaboration.inferenceFailed context
  where
    implicits =
      foldMap clauseImplicits clauses

-------------------------------------------------------------------------------

data Clause = Clause !Presyntax.Clause (Tsil Matching.Match)

clausePatterns :: Clause -> [Presyntax.PlicitPattern]
clausePatterns (Clause (Presyntax.Clause _ patterns _) _) =
  patterns

isEmpty :: Clause -> Bool
isEmpty clause =
  case clausePatterns clause of
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
clauseImplicits clause =
  case clausePatterns clause of
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
          (matches Tsil.:> Matching.Match value value Implicit (namedPats HashMap.! name) type_)

    _ ->
      Clause
        (Presyntax.Clause span patterns term)
        (matches Tsil.:> Matching.Match value value Implicit (Presyntax.Pattern span Presyntax.WildcardPattern) type_)

shiftExplicit :: Context v -> Domain.Value -> Domain.Type -> Clause -> M Clause
shiftExplicit context value type_ clause@(Clause (Presyntax.Clause span patterns term) matches) =
  case patterns of
    Presyntax.ExplicitPattern pat:patterns' ->
      pure $
        Clause
          (Presyntax.Clause span patterns' term)
          (matches Tsil.:> Matching.Match value value Explicit pat type_)

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

nextExplicitBinding :: Context v -> [Clause] -> M Binding
nextExplicitBinding context clauses = do
  (binding, _) <- SuggestedName.nextExplicit context $ clausePatterns <$> clauses
  pure binding

nextImplicitBinding :: Context v -> Name -> [Clause] -> M Binding
nextImplicitBinding context piName clauses = do
  (binding, _) <- SuggestedName.nextImplicit context piName $ clausePatterns <$> clauses
  pure binding
