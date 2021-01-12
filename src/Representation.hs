{-# language DeriveGeneric #-}
{-# language DeriveAnyClass #-}
module Representation where

import Data.Persist
import Protolude

data Signature
  = ConstantSignature !Representation
  | FunctionSignature [Representation] !Representation
  deriving (Show, Generic, Persist, Hashable)

data Representation
  = Empty
  | Direct
  | Indirect
  deriving (Eq, Ord, Show, Generic, Persist, Hashable)

instance Semigroup Representation where
  Empty <> representation = representation
  representation <> Empty = representation
  _ <> _ = Indirect

instance Monoid Representation where
  mempty =
    Empty

maxM :: Monad m => [m Representation] -> m Representation
maxM [] = pure Empty
maxM (m:ms) = do
  representation <- m
  case representation of
    Indirect ->
      pure Indirect

    _ ->
      max representation <$> maxM ms
