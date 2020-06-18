{-# language OverloadedStrings #-}
module Elaboration.Matching.SuggestedName where

import Protolude

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.HashSet as HashSet
import Rock

import Bindings (Bindings)
import qualified Bindings
import Context (Context)
import qualified Context
import Monad
import Name (Name(Name))
import qualified Name
import qualified Presyntax
import qualified Query
import qualified Scope
import qualified Span

nextExplicit
  :: Context v
  -> [[Presyntax.PlicitPattern]]
  -> M (Bindings, [[Presyntax.PlicitPattern]])
nextExplicit context clauses = do
  spannedNames <-
    concatMapM (concatMapM $ explicitNames context) $ maybeToList . headMay <$> clauses
  pure
    ( maybe "x" Bindings.Spanned $ NonEmpty.nonEmpty spannedNames
    , shiftExplicit <$> clauses
    )

explicitNames :: Context v -> Presyntax.PlicitPattern -> M [(Span.Relative, Name)]
explicitNames context pattern_ =
  case pattern_ of
    Presyntax.ExplicitPattern pattern' ->
      patternNames context pattern'

    _ ->
      pure []

shiftExplicit :: [Presyntax.PlicitPattern] -> [Presyntax.PlicitPattern]
shiftExplicit patterns =
  case patterns of
    Presyntax.ExplicitPattern _:patterns' ->
      patterns'

    Presyntax.ImplicitPattern _ _:patterns' ->
      shiftExplicit patterns'

    [] ->
      []

nextImplicit
  :: Context v
  -> Name
  -> [[Presyntax.PlicitPattern]]
  -> M (Bindings, [[Presyntax.PlicitPattern]])
nextImplicit context piName clauses = do
  spannedNames <-
    concatMapM (concatMapM $ implicitNames context piName) $ maybeToList . headMay <$> clauses
  pure
    ( maybe (Bindings.Unspanned piName) Bindings.Spanned $ NonEmpty.nonEmpty spannedNames
    , shiftImplicit piName <$> clauses
    )

implicitNames :: Context v -> Name -> Presyntax.PlicitPattern -> M [(Span.Relative, Name)]
implicitNames context piName pattern_ =
  case pattern_ of
    Presyntax.ImplicitPattern _ namedPats
      | Just pattern' <- HashMap.lookup piName namedPats ->
        patternNames context pattern'

    _ ->
      pure []

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

patternNames :: Context v -> Presyntax.Pattern -> M [(Span.Relative, Name)]
patternNames context pattern_ =
  case pattern_ of
    Presyntax.Pattern span (Presyntax.ConOrVar _ prename@(Name.Pre nameText) []) -> do
      maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) prename
      if HashSet.null $ foldMap Scope.entryConstructors maybeScopeEntry then
        pure [(span, Name nameText)]

      else
        pure []

    _ ->
      pure []

patternBinding :: Context v -> Presyntax.Pattern -> Name -> M Bindings
patternBinding context pattern_ fallbackName = do
  spannedNames <- patternNames context pattern_
  pure $
    maybe (Bindings.Unspanned fallbackName) Bindings.Spanned $
    NonEmpty.nonEmpty spannedNames
