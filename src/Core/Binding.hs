{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language TupleSections #-}
module Core.Binding where

import Protolude

import Data.Persist

import qualified Surface.Syntax as Surface
import Name (Name(Name))
import qualified Name
import qualified Span

data Binding
  = Spanned !Span.Relative !Name
  | Unspanned !Name
  deriving (Eq, Show, Generic, Persist, Hashable)

toName :: Binding -> Name
toName bindings =
  case bindings of
    Spanned _ name ->
      name

    Unspanned name ->
      name

fromSurface :: Surface.SpannedName -> Binding
fromSurface (Surface.SpannedName span (Name.Surface name)) =
  Spanned span $ Name name

spans :: Binding -> [Span.Relative]
spans binding =
  case binding of
    Spanned span _ ->
      [span]

    Unspanned _ ->
      []
