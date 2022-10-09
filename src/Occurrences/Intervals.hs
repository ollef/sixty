{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Occurrences.Intervals where

import Core.Binding (Binding)
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IntervalMap.FingerTree (IntervalMap)
import qualified Data.IntervalMap.FingerTree as IntervalMap
import qualified Data.List as List
import Data.Persist
import qualified Data.Text.Unsafe as Text
import Literal (Literal)
import qualified Name
import Orphans ()
import qualified Position
import Protolude
import qualified Span
import Var (Var)

data Item
  = Global Name.Qualified
  | Con Name.QualifiedConstructor
  | Lit Literal
  | Var Var
  deriving (Show, Eq, Generic, Hashable, Persist)

data Intervals = Intervals
  { _intervals :: IntervalMap Position.Relative Item
  , _items :: HashMap Item (HashSet Span.Relative)
  , _varBindingSpans :: EnumMap Var (NonEmpty Span.Relative)
  }
  deriving (Eq, Show, Generic, Persist, Hashable)

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
    Binding.Spanned span _ -> do
      singleton span (Var var)
        <> Intervals mempty mempty (EnumMap.singleton var $ pure span)
    Binding.Unspanned _ ->
      mempty

bindings :: Bindings -> Var -> Intervals
bindings b var =
  case b of
    Bindings.Spanned spannedNames -> do
      let spans =
            fst <$> spannedNames

      foldMap (\span -> singleton span $ Var var) spans
        <> Intervals mempty mempty (EnumMap.singleton var spans)
    Bindings.Unspanned _ ->
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
  case EnumMap.lookup var (_varBindingSpans intervals) of
    Nothing ->
      Nothing
    Just bindingSpans -> do
      let sortedBindingSpans =
            sortOn spanStart $ toList bindingSpans

          befores =
            List.takeWhile ((<= position) . spanStart) sortedBindingSpans

      lastMay befores

varSpans :: Var -> Position.Relative -> Intervals -> [Span.Relative]
varSpans var position intervals = do
  let candidates =
        itemSpans (Var var) intervals
  case EnumMap.lookup var (_varBindingSpans intervals) of
    Nothing ->
      candidates
    Just bindingSpans -> do
      let sortedBindingSpans =
            sortOn spanStart $ toList bindingSpans

          (befores, afters) =
            List.span ((<= position) . spanStart) sortedBindingSpans

      case reverse befores of
        [] ->
          candidates
        before : _ -> do
          let candidates' =
                filter ((>= spanStart before) . spanStart) candidates

          case afters of
            [] ->
              candidates'
            after : _ ->
              filter ((< spanStart after) . spanStart) candidates'

spanStart :: Span.Relative -> Position.Relative
spanStart (Span.Relative s _) =
  s

nameSpan :: Item -> Span.LineColumn -> Span.LineColumn
nameSpan
  item
  span@(Span.LineColumns _ (Position.LineColumn endLine endColumn)) =
    case item of
      Global (Name.Qualified _ (Name.Name name)) ->
        Span.LineColumns
          (Position.LineColumn endLine (endColumn - Text.lengthWord16 name))
          (Position.LineColumn endLine endColumn)
      Con (Name.QualifiedConstructor _ (Name.Constructor name)) ->
        Span.LineColumns
          (Position.LineColumn endLine (endColumn - Text.lengthWord16 name))
          (Position.LineColumn endLine endColumn)
      Lit _ ->
        span
      Var _ ->
        span
