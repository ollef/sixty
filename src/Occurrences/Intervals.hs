{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
module Occurrences.Intervals where

import Protolude hiding (IntMap)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.HashSet as HashSet
import Data.IntervalMap.FingerTree (IntervalMap)
import qualified Data.List as List
import qualified Data.IntervalMap.FingerTree as IntervalMap

import qualified Name
import qualified Position
import Binding (Binding)
import qualified Binding
import qualified Span
import Var (Var)
import qualified Var

data Item
  = Global Name.Qualified
  | Con Name.QualifiedConstructor
  | Var Var
  deriving (Show, Eq, Generic, Hashable)

data Intervals = Intervals
  { _intervals :: IntervalMap Position.Relative Item
  , _items :: HashMap Item (HashSet Span.Relative)
  , _varBindingSpans :: IntMap Var (NonEmpty Span.Relative)
  } deriving (Show, Generic)

instance Hashable Intervals where
  hashWithSalt salt (Intervals a b c) =
    salt `hashWithSalt`
      [ (i, j, k)
      | (IntervalMap.Interval i j, k) <-
        IntervalMap.intersections
        (fromMaybe (IntervalMap.Interval 0 0) $ IntervalMap.bounds a)
        a
      ]
      `hashWithSalt` b
      `hashWithSalt` c

instance Semigroup Intervals where
  Intervals a1 b1 c1 <> Intervals a2 b2 c2 =
    Intervals (a1 <> a2) (HashMap.unionWith (<>) b1 b2) (c1 <> c2)

instance Monoid Intervals where
  mempty =
    Intervals mempty mempty mempty

singleton :: Span.Relative -> Item -> Intervals
singleton span@(Span.Relative start end) item =
  Intervals
    { _intervals = IntervalMap.singleton (IntervalMap.Interval start (end - 1)) item
    , _items = HashMap.singleton item $ HashSet.singleton span
    , _varBindingSpans = mempty
    }

binding :: Binding -> Var -> Intervals
binding b var =
  case b of
    Binding.Spanned spannedNames -> do
      let
        spans =
          fst <$> spannedNames

      foldMap (\span -> singleton span $ Var var) spans
        <> Intervals mempty mempty (IntMap.singleton var spans)

    Binding.Unspanned _ ->
      mempty

null :: Intervals -> Bool
null =
  HashMap.null . _items

intersect :: Position.Relative -> Intervals -> [Item]
intersect pos (Intervals intervalMap _ _) = do
  (_, item) <- IntervalMap.search pos intervalMap
  pure item

itemSpans :: Item -> Intervals -> [Span.Relative]
itemSpans item (Intervals _ items _) =
  foldMap toList $ HashMap.lookup item items

bindingSpan :: Var -> Position.Relative -> Intervals -> Maybe Span.Relative
bindingSpan var position intervals =
  case IntMap.lookup var (_varBindingSpans intervals) of
    Nothing ->
      Nothing

    Just bindingSpans -> do
      let
        sortedBindingSpans =
          sortOn spanStart $ toList bindingSpans

        befores =
          List.takeWhile ((<= position) . spanStart) sortedBindingSpans

      lastMay befores

varSpans :: Var -> Position.Relative -> Intervals -> [Span.Relative]
varSpans var position intervals = do
  let
    candidates =
      itemSpans (Var var) intervals
  case IntMap.lookup var (_varBindingSpans intervals) of
    Nothing ->
      candidates

    Just bindingSpans -> do
      let
        sortedBindingSpans =
          sortOn spanStart $ toList bindingSpans

        (befores, afters) =
          List.span ((<= position) . spanStart) sortedBindingSpans

      case reverse befores of
        [] ->
          candidates

        before:_ -> do
          let
            candidates' =
              filter ((>= spanStart before) . spanStart) candidates

          case afters of
            [] ->
              candidates'

            after:_ ->
              filter ((< spanStart after) . spanStart) candidates'

spanStart :: Span.Relative -> Position.Relative
spanStart (Span.Relative s _) =
  s
