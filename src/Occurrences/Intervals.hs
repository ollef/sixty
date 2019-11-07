{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
module Occurrences.Intervals where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import Data.IntervalMap.FingerTree (IntervalMap)
import Data.IntervalMap.FingerTree as IntervalMap

import qualified Name
import qualified Position
import qualified Span
import Var (Var)

data Item
  = Global Name.Qualified
  | Con Name.QualifiedConstructor
  | Var Var
  deriving (Show, Eq, Generic, Hashable)

data Intervals = Intervals
  { _intervals :: IntervalMap Position.Relative Item
  , _items :: HashMap Item (HashSet Span.Relative)
  } deriving (Show, Generic)

instance Hashable Intervals where
  hashWithSalt salt (Intervals a b) =
    salt `hashWithSalt`
      [ (i, j, k)
      | (IntervalMap.Interval i j, k) <-
        IntervalMap.intersections
        (fromMaybe (IntervalMap.Interval 0 0) $ IntervalMap.bounds a)
        a
      ]
      `hashWithSalt` b

instance Semigroup Intervals where
  Intervals a1 b1 <> Intervals a2 b2 =
    Intervals (a1 <> a2) (HashMap.unionWith (<>) b1 b2)

instance Monoid Intervals where
  mempty =
    Intervals mempty mempty

null :: Intervals -> Bool
null =
  HashMap.null . _items

intersect :: Position.Relative -> Intervals -> [Item]
intersect pos (Intervals intervalMap _) = do
  (_, item) <- IntervalMap.search pos intervalMap
  pure item

itemSpans :: Item -> Intervals -> [Span.Relative]
itemSpans item (Intervals _ items) =
  foldMap toList $ HashMap.lookup item items
