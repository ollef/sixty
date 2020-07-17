{-# language DuplicateRecordFields #-}
{-# language ViewPatterns #-}
module Elaboration.Clauses where

import Protolude hiding (check, force)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import {-# SOURCE #-} qualified Elaboration
import Core.Binding (Binding)
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Syntax as Syntax
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import qualified Elaboration.Matching as Matching
import qualified Elaboration.Matching.SuggestedName as SuggestedName
import qualified Elaboration.Unification as Unification
import qualified Error
import Monad
import Name (Name)
import Plicity
import qualified Surface.Syntax as Surface

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
        | Clause (Surface.Clause span _ rhs) matches <- clauses
        ]
    Matching.elaborateClauses context matchingClauses expectedType

  | otherwise = do
    expectedType' <- Context.forceHead context expectedType
    case expectedType' of
      Domain.Pi _piBinding domain Explicit targetClosure
        | HashMap.null implicits -> do
          bindings <- nextExplicitBindings context clauses
          (context', var) <- Context.extend context (Bindings.toName bindings) domain
          target <-
            Evaluation.evaluateClosure
              targetClosure
              (Domain.var var)
          explicitFunCase context' bindings var domain target

      Domain.Fun domain Explicit target
        | HashMap.null implicits -> do
          bindings <- nextExplicitBindings context clauses
          (context', var) <- Context.extend context (Bindings.toName bindings) domain
          explicitFunCase context' bindings var domain target

      Domain.Pi piBinding domain Implicit targetClosure -> do
        bindings <- nextImplicitBindings context piBinding clauses
        (context', var) <- Context.extend context (Bindings.toName bindings) domain
        let
          value =
            Domain.var var
        target <- Evaluation.evaluateClosure targetClosure value
        domain'' <- Elaboration.readback context domain
        body <- check context' (shiftImplicit piBinding value domain <$> clauses) target
        pure $ Syntax.Lam bindings domain'' Implicit body

      _ -> do
        (term', type_) <- infer context clauses
        f <- Unification.tryUnify context type_ expectedType
        pure $ f term'
  where
    implicits =
      foldMap clauseImplicits clauses

    explicitFunCase context' bindings var domain target = do
      domain'' <- Elaboration.readback context domain
      clauses' <- mapM (shiftExplicit context (Domain.var var) domain) clauses
      body <- check context' clauses' target
      pure $ Syntax.Lam bindings domain'' Explicit body

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
        | Clause (Surface.Clause span _ rhs) matches <- clauses
        ]
    expectedType <- Context.newMetaType context
    result <- Matching.elaborateClauses context matchingClauses expectedType
    pure (result, expectedType)

  | otherwise =
    case HashMap.toList implicits of
      [] -> do
        domain <- Context.newMetaType context
        domain' <- Elaboration.readback context domain
        bindings <- nextExplicitBindings context clauses
        let
          name =
            Bindings.toName bindings
        (context', var) <- Context.extend context name domain
        clauses' <- mapM (shiftExplicit context (Domain.var var) domain) clauses
        (body, target) <- infer context' clauses'
        target' <- Elaboration.readback context' target

        pure
          ( Syntax.Lam bindings domain' Explicit body
          , Domain.Pi (Binding.Unspanned name) domain Explicit
            $ Domain.Closure (Context.toEnvironment context) target'
          )

      [(piName, _)] -> do
        let
          piBinding =
            Binding.Unspanned piName
        bindings <- nextImplicitBindings context piBinding clauses
        domain <- Context.newMetaType context
        domain' <- Elaboration.readback context domain
        (context', var) <- Context.extend context piName domain
        let
          value =
            Domain.var var
        (body, target) <- infer context' (shiftImplicit (Binding.Unspanned piName) value domain <$> clauses)
        target' <- Elaboration.readback context' target

        pure
          ( Syntax.Lam bindings domain' Implicit body
          , Domain.Pi piBinding domain Implicit
            $ Domain.Closure (Context.toEnvironment context) target'
          )

      _ -> do
        Context.report context Error.UnableToInferImplicitLambda
        Elaboration.inferenceFailed context
  where
    implicits =
      foldMap clauseImplicits clauses

-------------------------------------------------------------------------------

data Clause = Clause !Surface.Clause (Tsil Matching.Match)

clausePatterns :: Clause -> [Surface.PlicitPattern]
clausePatterns (Clause (Surface.Clause _ patterns _) _) =
  patterns

isEmpty :: Clause -> Bool
isEmpty clause =
  case clausePatterns clause of
    [] ->
      True

    _:_ ->
      False

removeEmptyImplicits :: Clause -> Clause
removeEmptyImplicits clause@(Clause (Surface.Clause span patterns term) matches) =
  case patterns of
    Surface.ImplicitPattern _ namedPats:patterns'
      | HashMap.null namedPats ->
        removeEmptyImplicits $ Clause (Surface.Clause span patterns' term) matches

    _ ->
      clause

clauseImplicits :: Clause -> HashMap Name Surface.Pattern
clauseImplicits clause =
  case clausePatterns clause of
    Surface.ImplicitPattern _ namedPats:_ ->
      namedPats

    _ ->
      mempty

shiftImplicit :: Binding -> Domain.Value -> Domain.Type -> Clause -> Clause
shiftImplicit binding value type_ (Clause (Surface.Clause span patterns term) matches) =
  case patterns of
    Surface.ImplicitPattern patSpan namedPats:patterns'
      | let name = Binding.toName binding
      , HashMap.member name namedPats ->
        Clause
          (Surface.Clause
            span
            (Surface.ImplicitPattern patSpan (HashMap.delete name namedPats):patterns')
            term
          )
          (matches Tsil.:> Matching.Match value value Implicit (namedPats HashMap.! name) type_)

    _ ->
      Clause
        (Surface.Clause span patterns term)
        (matches Tsil.:> Matching.Match value value Implicit (Surface.Pattern span Surface.WildcardPattern) type_)

shiftExplicit :: Context v -> Domain.Value -> Domain.Type -> Clause -> M Clause
shiftExplicit context value type_ clause@(Clause (Surface.Clause span patterns term) matches) =
  case patterns of
    Surface.ExplicitPattern pat:patterns' ->
      pure $
        Clause
          (Surface.Clause span patterns' term)
          (matches Tsil.:> Matching.Match value value Explicit pat type_)

    Surface.ImplicitPattern patSpan _:patterns' -> do
      Context.report
        (Context.spanned patSpan context)
        (Error.PlicityMismatch Error.Argument $ Error.Mismatch Explicit Implicit)
      shiftExplicit
        context
        value
        type_
        (Clause
          (Surface.Clause span patterns' term)
          matches
        )

    [] -> do
      Context.report
        (Context.spanned span context)
        (Error.PlicityMismatch Error.Argument $ Error.Missing Explicit)
      pure clause

nextExplicitBindings :: Context v -> [Clause] -> M Bindings
nextExplicitBindings context clauses = do
  (bindings, _) <- SuggestedName.nextExplicit context $ clausePatterns <$> clauses
  pure bindings

nextImplicitBindings :: Context v -> Binding -> [Clause] -> M Bindings
nextImplicitBindings context piBinding clauses = do
  (bindings, _) <- SuggestedName.nextImplicit context (Binding.toName piBinding) $ clausePatterns <$> clauses
  pure bindings
