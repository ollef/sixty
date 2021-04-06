{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

module Core.Bindings where

import qualified Data.List.NonEmpty as NonEmpty
import Data.Persist
import Data.String
import Name (Name)
import Protolude
import qualified Span

data Bindings
  = Spanned (NonEmpty (Span.Relative, Name))
  | Unspanned !Name
  deriving (Eq, Show, Generic, Persist, Hashable)

toName :: Bindings -> Name
toName bindings =
  case bindings of
    Spanned ((_, name) NonEmpty.:| _) ->
      name
    Unspanned name ->
      name

fromName :: [Span.Relative] -> Name -> Bindings
fromName spans_ name =
  case spans_ of
    [] ->
      Unspanned name
    span : spans' ->
      Spanned $ (span, name) NonEmpty.:| ((,name) <$> spans')

spans :: Bindings -> [Span.Relative]
spans binding =
  case binding of
    Spanned spannedNames ->
      toList $ fst <$> spannedNames
    Unspanned _ ->
      []

instance IsString Bindings where
  fromString =
    Unspanned . fromString
