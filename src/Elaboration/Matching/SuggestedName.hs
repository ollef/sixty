{-# language OverloadedStrings #-}
module Elaboration.Matching.SuggestedName where

import Protolude

import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Rock

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
  -> M (Name, [[Presyntax.PlicitPattern]])
nextExplicit context clauses = do
  maybeName <- runMaybeT $ asum $ explicitVarName context <$> clauses
  pure (fromMaybe "x" maybeName, shiftExplicit <$> clauses)

explicitVarName :: Context v -> [Presyntax.PlicitPattern] -> MaybeT M Name
explicitVarName context patterns =
  case patterns of
    Presyntax.ExplicitPattern (Presyntax.Pattern _ (Presyntax.ConOrVar prename@(Name.Pre nameText) [])):_ -> do
      maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) prename
      if HashSet.null $ foldMap Scope.entryConstructors maybeScopeEntry then
        pure $ Name nameText

      else
        empty

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
  -> M (Name, [[Presyntax.PlicitPattern]])
nextImplicit context piName clauses = do
  maybeName <- runMaybeT $ asum $ implicitVarName context piName <$> clauses
  pure (fromMaybe piName maybeName, shiftImplicit piName <$> clauses)

implicitVarName :: Context v -> Name -> [Presyntax.PlicitPattern] -> MaybeT M Name
implicitVarName context piName patterns =
  case patterns of
    Presyntax.ImplicitPattern _ namedPats:_
      | Just (Presyntax.Pattern _ (Presyntax.ConOrVar prename@(Name.Pre nameText) [])) <- HashMap.lookup piName namedPats -> do
        maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) prename
        if HashSet.null $ foldMap Scope.entryConstructors maybeScopeEntry then
          pure $ Name nameText

        else
          empty

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
