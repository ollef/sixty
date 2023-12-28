{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Representation where

import Prettyprinter
import Protolude

data Signature
  = ConstantSignature !Representation
  | FunctionSignature [Representation] !Representation
  deriving (Eq, Show, Generic, Hashable)

data Representation
  = Empty
  | Direct
  | Indirect
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Semigroup Representation where
  Empty <> representation = representation
  representation <> Empty = representation
  _ <> _ = Indirect

instance Monoid Representation where
  mempty = Empty

instance Pretty Representation where
  pretty = \case
    Empty -> "empty"
    Direct -> "direct"
    Indirect -> "indirect"

maxM :: Monad m => [m Representation] -> m Representation
maxM [] = pure mempty
maxM (m : ms) = do
  representation <- m
  case representation of
    Indirect ->
      pure representation
    _ ->
      max representation <$> maxM ms
