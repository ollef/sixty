{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Orphans where

import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.EnumSet (EnumSet)
import qualified Data.EnumSet as EnumSet
import Data.IntervalMap.FingerTree (IntervalMap)
import qualified Data.IntervalMap.FingerTree as IntervalMap
import Data.Text.Utf16.Rope (Rope)
import qualified Data.Text.Utf16.Rope as Rope
import Protolude hiding (IntSet, get, put)

instance (Enum k, Hashable k, Hashable v) => Hashable (EnumMap k v) where
  hashWithSalt s = hashWithSalt s . EnumMap.toList

instance (Enum k, Hashable k) => Hashable (EnumSet k) where
  hashWithSalt s = hashWithSalt s . EnumSet.toList

instance Hashable k => Hashable (IntervalMap.Interval k) where
  hashWithSalt s (IntervalMap.Interval a b) =
    hashWithSalt s (a, b)

instance (Hashable k, Ord k, Hashable v) => Hashable (IntervalMap k v) where
  hashWithSalt s m =
    hashWithSalt s $
      (`IntervalMap.intersections` m)
        <$> IntervalMap.bounds m

instance Hashable Rope where
  hashWithSalt s = hashWithSalt s . Rope.toText
