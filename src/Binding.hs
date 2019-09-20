{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Binding where

import Protolude

import Data.String

import Name (Name)
import qualified Span
import qualified Presyntax

data Binding
  = Spanned !Span.Relative !Name
  | Unspanned !Name
  deriving (Eq, Show, Generic, Hashable)

toName :: Binding -> Name
toName binding =
  case binding of
    Spanned _ name ->
      name

    Unspanned name ->
      name

span :: Binding -> Maybe Span.Relative
span binding =
  case binding of
    Spanned s _ ->
      Just s

    Unspanned _ ->
      Nothing

fromPresyntax :: Presyntax.Binding -> Binding
fromPresyntax (Presyntax.Binding span_ name) =
  Spanned span_ name

instance IsString Binding where
  fromString =
    Unspanned . fromString
