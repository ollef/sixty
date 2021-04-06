{-# LANGUAGE OverloadedStrings #-}

module Elaboration.Matching.SuggestedName where

import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NonEmpty
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import Monad
import Name (Name (Name))
import qualified Name
import Protolude
import qualified Query
import Rock
import qualified Scope
import qualified Span
import qualified Surface.Syntax as Surface

nextExplicit ::
  Context v ->
  [[Surface.PlicitPattern]] ->
  M (Bindings, [[Surface.PlicitPattern]])
nextExplicit context clauses = do
  spannedNames <-
    concatMapM (concatMapM $ explicitNames context) $ maybeToList . headMay <$> clauses
  pure
    ( maybe "x" Bindings.Spanned $ NonEmpty.nonEmpty spannedNames
    , shiftExplicit <$> clauses
    )

explicitNames :: Context v -> Surface.PlicitPattern -> M [(Span.Relative, Name)]
explicitNames context pattern_ =
  case pattern_ of
    Surface.ExplicitPattern pattern' ->
      patternNames context pattern'
    _ ->
      pure []

shiftExplicit :: [Surface.PlicitPattern] -> [Surface.PlicitPattern]
shiftExplicit patterns =
  case patterns of
    Surface.ExplicitPattern _ : patterns' ->
      patterns'
    Surface.ImplicitPattern _ _ : patterns' ->
      shiftExplicit patterns'
    [] ->
      []

nextImplicit ::
  Context v ->
  Name ->
  [[Surface.PlicitPattern]] ->
  M (Bindings, [[Surface.PlicitPattern]])
nextImplicit context piName clauses = do
  spannedNames <-
    concatMapM (concatMapM $ implicitNames context piName) $ maybeToList . headMay <$> clauses
  pure
    ( maybe (Bindings.Unspanned piName) Bindings.Spanned $ NonEmpty.nonEmpty spannedNames
    , shiftImplicit piName <$> clauses
    )

implicitNames :: Context v -> Name -> Surface.PlicitPattern -> M [(Span.Relative, Name)]
implicitNames context piName pattern_ =
  case pattern_ of
    Surface.ImplicitPattern _ namedPats
      | Just pattern' <- HashMap.lookup piName namedPats ->
        patternNames context pattern'
    _ ->
      pure []

shiftImplicit :: Name -> [Surface.PlicitPattern] -> [Surface.PlicitPattern]
shiftImplicit name patterns =
  case patterns of
    Surface.ImplicitPattern patSpan namedPats : patterns' ->
      let namedPats' =
            HashMap.delete name namedPats
       in if HashMap.null namedPats'
            then patterns'
            else Surface.ImplicitPattern patSpan namedPats' : patterns'
    _ ->
      patterns

patternNames :: Context v -> Surface.Pattern -> M [(Span.Relative, Name)]
patternNames context pattern_ =
  case pattern_ of
    Surface.Pattern span (Surface.ConOrVar (Surface.SpannedName _ surfaceName@(Name.Surface nameText)) []) -> do
      maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) surfaceName
      if HashSet.null $ foldMap Scope.entryConstructors maybeScopeEntry
        then pure [(span, Name nameText)]
        else pure []
    _ ->
      pure []

patternBinding :: Context v -> Surface.Pattern -> Name -> M Bindings
patternBinding context pattern_ fallbackName = do
  spannedNames <- patternNames context pattern_
  pure $
    maybe (Bindings.Unspanned fallbackName) Bindings.Spanned $
      NonEmpty.nonEmpty spannedNames
