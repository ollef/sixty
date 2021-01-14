{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Representation where

import Data.Persist
import Data.Text.Prettyprint.Doc
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

instance Pretty Representation where
  pretty representation =
    case representation of
      Empty ->
        "empty"

      Direct ->
        "direct"

      Indirect ->
        "indirect"

maxM :: Monad m => [m Representation] -> m Representation
maxM [] = pure Empty
maxM (m:ms) = do
  representation <- m
  case representation of
    Indirect ->
      pure Indirect

    _ ->
      max representation <$> maxM ms
