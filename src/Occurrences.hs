{-# language DuplicateRecordFields #-}
{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
module Occurrences where

import Protolude hiding (moduleName)

import Rock

import Core.Binding (Binding)
import Core.Bindings (Bindings)
import Data.OrderedHashMap as OrderedHashMap
import qualified Core.Domain as Domain
import Environment (Environment)
import qualified Environment
import qualified Index
import Literal (Literal)
import qualified Monad
import qualified Name
import Occurrences.Intervals (Intervals)
import qualified Occurrences.Intervals as Intervals
import qualified Surface.Syntax as Surface
import qualified Query
import Query (Query)
import qualified Query.Mapped as Mapped
import qualified Scope
import qualified Span
import qualified Core.Syntax as Syntax
import Telescope (Telescope)
import qualified Telescope
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

      Just (Syntax.DataDefinition _ tele, _, _) ->
        dataDefinitionOccurrences env tele
  where
    definitionNameOccurrences :: M Intervals
    definitionNameOccurrences = do
      constructorSpans <- definitionConstructorSpans key qualifiedName
      spans <- definitionNameSpans key qualifiedName
      pure $ mconcat $
        foreach constructorSpans (\(span, con) -> Intervals.singleton span $ Intervals.Con con) <>
        foreach spans (`Intervals.singleton` Intervals.Global qualifiedName)

definitionNameSpans :: MonadFetch Query m => Scope.Key -> Name.Qualified -> m [Span.Relative]
definitionNameSpans key (Name.Qualified moduleName name) = do
  maybeParsedDefinition <- fetch $ Query.ParsedDefinition moduleName $ Mapped.Query (key, name)
  pure $ foldMap Surface.spans maybeParsedDefinition

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
        second (Name.QualifiedConstructor qualifiedName) <$> Surface.constructorSpans parsedDefinition

termOccurrences
  :: Domain.Environment v
  -> Maybe Span.Relative
  -> Syntax.Term v
  -> M Intervals
termOccurrences env maybeSpan term =
  case term of
    Syntax.Var index ->
      pure $ foldMap (\span -> Intervals.singleton span $ Intervals.Var $ Environment.lookupIndexVar index env) maybeSpan

    Syntax.Global global ->
      pure $ foldMap (\span -> Intervals.singleton span $ Intervals.Global global) maybeSpan

    Syntax.Con con ->
      pure $ foldMap (\span -> Intervals.singleton span $ Intervals.Con con) maybeSpan

    Syntax.Lit lit ->
      pure $ foldMap (\span -> Intervals.singleton span $ Intervals.Lit lit) maybeSpan

    Syntax.Meta _ ->
      mempty

    Syntax.Let bindings term' type_ body -> do
      (env', var) <- extend env
      bindingsOccurrences bindings var <>
        termOccurrences env Nothing term' <>
        termOccurrences env Nothing type_ <>
        termOccurrences env' Nothing body

    Syntax.Pi binding domain _ target -> do
      (env', var) <- extend env
      bindingOccurrences binding var <>
        termOccurrences env Nothing domain <>
        termOccurrences env' Nothing target

    Syntax.Fun domain _ target ->
      termOccurrences env Nothing domain <>
      termOccurrences env Nothing target

    Syntax.Lam binding type_ _ body -> do
      (env', var) <- extend env
      bindingsOccurrences binding var <>
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
      branchesOccurrences env branches <>
      foldMap (termOccurrences env Nothing) defaultBranch

    Syntax.Spanned span term' ->
      termOccurrences env (Just span) term'

dataDefinitionOccurrences
  :: Domain.Environment v
  -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
  -> M Intervals
dataDefinitionOccurrences env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) ->
      foldMap (termOccurrences env Nothing) $ OrderedHashMap.elems constrDefs

    Telescope.Extend binding type_ _ tele' -> do
      (env', var) <- extend env
      bindingOccurrences binding var <>
        termOccurrences env Nothing type_ <>
        dataDefinitionOccurrences env' tele'

branchesOccurrences
  :: Domain.Environment v
  -> Syntax.Branches v
  -> M Intervals
branchesOccurrences env branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      foldMap (constructorBranchOccurrences env constructorTypeName) $ OrderedHashMap.toList constructorBranches

    Syntax.LiteralBranches literalBranches ->
      foldMap (literalBranchOccurrences env) $ OrderedHashMap.toList literalBranches

constructorBranchOccurrences
  :: Domain.Environment v
  -> Name.Qualified
  -> (Name.Constructor, ([Span.Relative], Telescope Bindings Syntax.Type Syntax.Term v))
  -> M Intervals
constructorBranchOccurrences env constructorTypeName (constr, (spans, tele)) =
  pure (mconcat [Intervals.singleton span $ Intervals.Con (Name.QualifiedConstructor constructorTypeName constr) | span <- spans]) <>
    telescopeOccurrences env tele

literalBranchOccurrences
  :: Domain.Environment v
  -> (Literal, ([Span.Relative], Syntax.Term v))
  -> M Intervals
literalBranchOccurrences env (lit, (spans, body)) =
  pure (mconcat [Intervals.singleton span $ Intervals.Lit lit | span <- spans]) <> 
    termOccurrences env Nothing body

telescopeOccurrences
  :: Domain.Environment v
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> M Intervals
telescopeOccurrences env tele =
  case tele of
    Telescope.Empty branch ->
      termOccurrences env Nothing branch

    Telescope.Extend bindings type_ _ tele' -> do
      (env', var) <- extend env
      bindingsOccurrences bindings var <>
        termOccurrences env Nothing type_ <>
        telescopeOccurrences env' tele'

bindingOccurrences
  :: Binding
  -> Var
  -> M Intervals
bindingOccurrences binding var =
  pure $ Intervals.binding binding var

bindingsOccurrences
  :: Bindings
  -> Var
  -> M Intervals
bindingsOccurrences bindings var =
  pure $ Intervals.bindings bindings var
