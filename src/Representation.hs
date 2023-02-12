{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Representation where

import Data.Persist
import Prettyprinter
import Protolude

data Signature
  = ConstantSignature !Representation
  | FunctionSignature [Representation] !Representation
  deriving (Eq, Show, Generic, Persist, Hashable)

data Representation
  = Empty
  | Direct !ContainsHeapPointers
  | Indirect !ContainsHeapPointers
  deriving (Eq, Ord, Show, Generic, Persist, Hashable)

data ContainsHeapPointers
  = Doesn'tContainHeapPointers
  | MightContainHeapPointers
  deriving (Eq, Ord, Show, Generic, Persist, Hashable)

instance Semigroup Representation where
  Empty <> representation = representation
  representation <> Empty = representation
  representation1 <> representation2 =
    Indirect $ containsHeapPointers representation1 <> containsHeapPointers representation2

containsHeapPointers :: Representation -> ContainsHeapPointers
containsHeapPointers Empty = Doesn'tContainHeapPointers
containsHeapPointers (Direct cp) = cp
containsHeapPointers (Indirect cp) = cp

instance Monoid Representation where
  mempty =
    Empty

instance Pretty Representation where
  pretty representation =
    case representation of
      Empty ->
        "empty"
      Direct MightContainHeapPointers ->
        "direct*"
      Direct Doesn'tContainHeapPointers ->
        "direct"
      Indirect MightContainHeapPointers ->
        "indirect*"
      Indirect Doesn'tContainHeapPointers ->
        "indirect"

instance Semigroup ContainsHeapPointers where
  MightContainHeapPointers <> _ = MightContainHeapPointers
  _ <> MightContainHeapPointers = MightContainHeapPointers
  Doesn'tContainHeapPointers <> Doesn'tContainHeapPointers = Doesn'tContainHeapPointers

instance Monoid ContainsHeapPointers where
  mempty = Doesn'tContainHeapPointers

maxM :: Monad m => [m Representation] -> m Representation
maxM [] = pure mempty
maxM (m : ms) = do
  representation <- m
  case representation of
    Indirect MightContainHeapPointers ->
      pure representation
    _ ->
      max representation <$> maxM ms
