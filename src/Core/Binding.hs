{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

module Core.Binding where

import Data.String
import Name (Name (Name))
import qualified Name
import Protolude
import qualified Span
import qualified Surface.Syntax as Surface

data Binding
  = Spanned !Span.Relative !Name
  | Unspanned !Name
  deriving (Eq, Show, Generic, Hashable)

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

instance IsString Binding where
  fromString =
    Unspanned . fromString
