{-# language OverloadedStrings #-}
module Elaboration.Matching.SuggestedName where

import Protolude

import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Rock

import Binding (Binding)
import qualified Binding
import Context (Context)
import qualified Context
import Monad
import Name (Name(Name))
import qualified Name
import qualified Presyntax
import qualified Query
import qualified Scope

nextExplicit
  :: Context v
  -> [[Presyntax.PlicitPattern]]
  -> M (Binding, [[Presyntax.PlicitPattern]])
nextExplicit context clauses = do
  maybeBinding <-
    runMaybeT $ asum $ asum . fmap (explicitBinding context) <$> clauses
  pure (fromMaybe "x" maybeBinding, shiftExplicit <$> clauses)

explicitBinding :: Context v -> Presyntax.PlicitPattern -> MaybeT M Binding
explicitBinding context pattern =
  case pattern of
    Presyntax.ExplicitPattern pattern' ->
      patternBinding context pattern'

    _ ->
      empty

shiftExplicit :: [Presyntax.PlicitPattern] -> [Presyntax.PlicitPattern]
shiftExplicit patterns =
  case patterns of
    Presyntax.ExplicitPattern _:patterns' ->
      patterns'

    Presyntax.ImplicitPattern _ _:patterns' -> do
      shiftExplicit patterns'

    [] ->
      []

nextImplicit
  :: Context v
  -> Name
  -> [[Presyntax.PlicitPattern]]
  -> M (Binding, [[Presyntax.PlicitPattern]])
nextImplicit context piName clauses = do
  maybeBinding <-
    runMaybeT $ asum $ asum . fmap (implicitBinding context piName) . headMay <$> clauses
  pure (fromMaybe (Binding.Unspanned piName) maybeBinding, shiftImplicit piName <$> clauses)

implicitBinding :: Context v -> Name -> Presyntax.PlicitPattern -> MaybeT M Binding
implicitBinding context piName pattern =
  case pattern of
    Presyntax.ImplicitPattern _ namedPats
      | Just pattern' <- HashMap.lookup piName namedPats -> do
        patternBinding context pattern'

    _ ->
      empty

shiftImplicit :: Name -> [Presyntax.PlicitPattern] -> [Presyntax.PlicitPattern]
shiftImplicit name patterns =
  case patterns of
    Presyntax.ImplicitPattern patSpan namedPats:patterns' ->
      let
        namedPats' =
          HashMap.delete name namedPats

      in
      if HashMap.null namedPats' then
        patterns'

      else
        Presyntax.ImplicitPattern patSpan namedPats':patterns'

    _ ->
      patterns

patternBinding :: Context v -> Presyntax.Pattern -> MaybeT M Binding
patternBinding context pattern =
  case pattern of
    Presyntax.Pattern span (Presyntax.ConOrVar prename@(Name.Pre nameText) []) -> do
      maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) prename
      if HashSet.null $ foldMap Scope.entryConstructors maybeScopeEntry then
        pure $ Binding.Spanned span $ Name nameText

      else
        empty

    _ ->
      empty
