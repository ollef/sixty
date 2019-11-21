{-# language DuplicateRecordFields #-}
{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
module Occurrences where

import Protolude hiding (moduleName)

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntervalMap.FingerTree as IntervalMap
import Rock

import Binding (Binding)
import qualified Binding
import qualified Domain
import Environment (Environment)
import qualified Environment
import qualified Index
import qualified Monad
import qualified Name
import Occurrences.Intervals (Intervals(Intervals))
import qualified Occurrences.Intervals as Intervals
import qualified Presyntax
import qualified Query
import Query (Query)
import qualified Query.Mapped as Mapped
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var (Var)

newtype M a = M { run :: Monad.M a }
  deriving (Functor, Applicative, Monad, MonadFetch Query)

instance Semigroup a => Semigroup (M a) where
  M m <> M n =
    M $ (<>) <$> m <*> n

instance Monoid a => Monoid (M a) where
  mempty =
    pure mempty

extend
  :: Environment value v
  -> M (Environment value (Index.Succ v), Var)
extend =
  M . Environment.extend

singleton :: Span.Relative -> Intervals.Item -> Intervals
singleton span@(Span.Relative start end) item =
  Intervals
    { _intervals = IntervalMap.singleton (IntervalMap.Interval start (end - 1)) item
    , _items = HashMap.singleton item $ HashSet.singleton span
    }

definitionOccurrences
  :: Domain.Environment Void
  -> Scope.Key
  -> Name.Qualified
  -> M Intervals
definitionOccurrences env key qualifiedName =
  definitionNameOccurrences <> do
    mdef <- fetch $ Query.ElaboratingDefinition $ Scope.KeyedName key qualifiedName
    case mdef of
      Nothing ->
        mempty

      Just (Syntax.TypeDeclaration type_, _, _) ->
        termOccurrences env Nothing type_

      Just (Syntax.ConstantDefinition term, _, _) ->
        termOccurrences env Nothing term

      Just (Syntax.DataDefinition tele, _, _) ->
        dataDefinitionOccurrences env tele
  where
    definitionNameOccurrences :: M Intervals
    definitionNameOccurrences = do
      constructorSpans <- definitionConstructorSpans key qualifiedName
      spans <- definitionNameSpans key qualifiedName
      pure $ mconcat $
        foreach constructorSpans (\(span, con) -> singleton span $ Intervals.Con con) <>
        foreach spans (`singleton` Intervals.Global qualifiedName)

definitionNameSpans :: MonadFetch Query m => Scope.Key -> Name.Qualified -> m [Span.Relative]
definitionNameSpans key (Name.Qualified moduleName name) = do
  maybeParsedDefinition <- fetch $ Query.ParsedDefinition moduleName $ Mapped.Query (key, name)
  pure $
    case maybeParsedDefinition of
      Nothing ->
        []

      Just parsedDefinition ->
        Presyntax.spans parsedDefinition

definitionConstructorSpans
  :: MonadFetch Query m
  => Scope.Key
  -> Name.Qualified
  -> m [(Span.Relative, Name.QualifiedConstructor)]
definitionConstructorSpans key qualifiedName@(Name.Qualified moduleName name) = do
  maybeParsedDefinition <- fetch $ Query.ParsedDefinition moduleName $ Mapped.Query (key, name)
  pure $
    case maybeParsedDefinition of
      Nothing ->
        []

      Just parsedDefinition ->
        second (Name.QualifiedConstructor qualifiedName) <$> Presyntax.constructorSpans parsedDefinition

termOccurrences
  :: Domain.Environment v
  -> Maybe Span.Relative
  -> Syntax.Term v
  -> M Intervals
termOccurrences env maybeSpan term =
  case term of
    Syntax.Var index ->
      pure $ foldMap (\span -> singleton span $ Intervals.Var $ Environment.lookupIndexVar index env) maybeSpan

    Syntax.Global global ->
      pure $ foldMap (\span -> singleton span $ Intervals.Global global) maybeSpan

    Syntax.Con con ->
      pure $ foldMap (\span -> singleton span $ Intervals.Con con) maybeSpan

    Syntax.Meta _ ->
      mempty

    Syntax.Let binding term' type_ body -> do
      (env', var) <- extend env
      bindingOccurrences binding var <>
        termOccurrences env Nothing term' <>
        termOccurrences env Nothing type_ <>
        termOccurrences env' Nothing body

    Syntax.Pi binding source _ target -> do
      (env', var) <- extend env
      bindingOccurrences binding var <>
        termOccurrences env Nothing source <>
        termOccurrences env' Nothing target

    Syntax.Fun source _ target ->
      termOccurrences env Nothing source <>
      termOccurrences env Nothing target

    Syntax.Lam binding type_ _ body -> do
      (env', var) <- extend env
      bindingOccurrences binding var <>
        termOccurrences env Nothing type_ <>
        termOccurrences env' Nothing body

    Syntax.App t1 _ t2 -> do
      intervals2 <- termOccurrences env Nothing t2
      if Intervals.null intervals2 then
        termOccurrences env maybeSpan t1

      else do
        intervals1 <- termOccurrences env Nothing t1
        pure $ intervals1 <> intervals2

    Syntax.Case scrutinee branches defaultBranch ->
      termOccurrences env Nothing scrutinee <>
      foldMap (branchOccurrences env) (HashMap.toList branches) <>
      foldMap (termOccurrences env Nothing) defaultBranch

    Syntax.Spanned span term' ->
      termOccurrences env (Just span) term'

dataDefinitionOccurrences
  :: Domain.Environment v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> M Intervals
dataDefinitionOccurrences env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) ->
      foldMap (termOccurrences env Nothing) $ HashMap.elems constrDefs

    Telescope.Extend binding type_ _ tele' -> do
      (env', var) <- extend env
      bindingOccurrences binding var <>
        termOccurrences env Nothing type_ <>
        dataDefinitionOccurrences env' tele'

branchOccurrences
  :: Domain.Environment v
  -> (Name.QualifiedConstructor, ([Span.Relative], Telescope Syntax.Type Syntax.Term v))
  -> M Intervals
branchOccurrences env (constr, (spans, tele)) =
  pure (mconcat [singleton span $ Intervals.Con constr | span <- spans]) <> teleOccurrences env tele

teleOccurrences
  :: Domain.Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> M Intervals
teleOccurrences env tele =
  case tele of
    Telescope.Empty branch ->
      termOccurrences env Nothing branch

    Telescope.Extend binding type_ _ tele' -> do
      (env', var) <- extend env
      bindingOccurrences binding var <>
        termOccurrences env Nothing type_ <>
        teleOccurrences env' tele'

bindingOccurrences
  :: Binding
  -> Var
  -> M Intervals
bindingOccurrences binding var =
  pure $ case binding of
    Binding.Spanned spannedNames -> do
      foldMap (\(span, _) -> singleton span $ Intervals.Var var) spannedNames

    Binding.Unspanned _ ->
      mempty
