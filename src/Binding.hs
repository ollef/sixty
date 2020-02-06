{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language TupleSections #-}
module Binding where

import Protolude

import Data.String
import qualified Data.List.NonEmpty as NonEmpty
import Data.Persist

import Name (Name)
import qualified Span
import qualified Presyntax

data Binding
  = Spanned !(NonEmpty (Span.Relative, Name))
  | Unspanned !Name
  deriving (Eq, Show, Generic, Persist, Hashable)

fromName :: [Span.Relative] -> Name -> Binding
fromName spans_ name =
  maybe (Unspanned name) (Spanned . fmap (, name)) $ NonEmpty.nonEmpty spans_

toName :: Binding -> Name
toName binding =
  case binding of
    Spanned spannedNames ->
      snd $ NonEmpty.head spannedNames

    Unspanned name ->
      name

spans :: Binding -> [Span.Relative]
spans binding =
  case binding of
    Spanned spannedNames ->
      toList $ fst <$> spannedNames

    Unspanned _ ->
      []

fromPresyntax :: Presyntax.Binding -> Binding
fromPresyntax (Presyntax.Binding span_ name) =
  Spanned $ pure (span_, name)

instance IsString Binding where
  fromString =
    Unspanned . fromString
