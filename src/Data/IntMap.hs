{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.IntMap where

import Data.Coerce
import qualified "containers" Data.IntMap.Lazy as Containers
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Protolude hiding (IntMap, IntSet)

newtype IntMap key value = IntMap (Containers.IntMap value)
  deriving (Functor, Foldable, Traversable, Eq, Ord, Read, Show, Semigroup, Monoid)

instance (Hashable key, Hashable value, Coercible Containers.Key key) => Hashable (IntMap key value) where
  hashWithSalt salt (IntMap m) = hashWithSalt salt (coerce $ Containers.toList m :: [(key, value)])

null :: IntMap key value -> Bool
null (IntMap m) =
  Containers.null m

singleton :: Coercible key Containers.Key => key -> value -> IntMap key value
singleton key value =
  IntMap $ Containers.singleton (coerce key) value

fromSet :: Coercible key Containers.Key => (key -> value) -> IntSet key -> IntMap key value
fromSet f (IntSet.IntSet set) =
  IntMap $ Containers.fromSet (coerce f) set

fromList :: Coercible key Containers.Key => [(key, value)] -> IntMap key value
fromList xs =
  IntMap $ Containers.fromList $ coerce xs

fromListWith :: Coercible key Containers.Key => (value -> value -> value) -> [(key, value)] -> IntMap key value
fromListWith f xs =
  IntMap $ Containers.fromListWith f $ coerce xs

toList :: Coercible key Containers.Key => IntMap key value -> [(key, value)]
toList (IntMap m) =
  coerce $ Containers.toList m

toDescList :: Coercible key Containers.Key => IntMap key value -> [(key, value)]
toDescList (IntMap m) =
  coerce $ Containers.toDescList m

insert :: Coercible key Containers.Key => key -> value -> IntMap key value -> IntMap key value
insert key value =
  coerce $ Containers.insert (coerce key) value

insertWith :: Coercible key Containers.Key => (value -> value -> value) -> key -> value -> IntMap key value -> IntMap key value
insertWith f key value =
  coerce $ Containers.insertWith f (coerce key) value

adjust :: Coercible key Containers.Key => (value -> value) -> key -> IntMap key value -> IntMap key value
adjust f key =
  coerce $ Containers.adjust f (coerce key)

alterF ::
  (Coercible key Containers.Key, Functor f) =>
  (Maybe value -> f (Maybe value)) ->
  key ->
  IntMap key value ->
  f (IntMap key value)
alterF f key m =
  coerce <$> Containers.alterF f (coerce key) (coerce m)

lookup :: Coercible key Containers.Key => key -> IntMap key value -> Maybe value
lookup key m =
  Containers.lookup (coerce key) (coerce m)

(!) :: Coercible key Containers.Key => IntMap key value -> key -> value
m ! key =
  coerce m Containers.! coerce key

lookupDefault :: Coercible key Containers.Key => value -> key -> IntMap key value -> value
lookupDefault def key m =
  Containers.findWithDefault def (coerce key) (coerce m)

delete :: Coercible key Containers.Key => key -> IntMap key value -> IntMap key value
delete key (IntMap m) =
  coerce $ Containers.delete (coerce key) m

member :: Coercible key Containers.Key => key -> IntMap key value -> Bool
member key (IntMap m) =
  Containers.member (coerce key) m

unionWith :: (value -> value -> value) -> IntMap key value -> IntMap key value -> IntMap key value
unionWith f m1 m2 =
  IntMap $ Containers.unionWith f (coerce m1) (coerce m2)

difference :: IntMap key value1 -> IntMap key value2 -> IntMap key value1
difference (IntMap m1) (IntMap m2) =
  IntMap $ Containers.difference m1 m2

traverseWithKey :: (Coercible key Containers.Key, Applicative t) => (key -> value1 -> t value2) -> IntMap key value1 -> t (IntMap key value2)
traverseWithKey f (IntMap m) =
  IntMap <$> Containers.traverseWithKey (coerce f) m

keys :: (Coercible key Containers.Key) => IntMap key value -> [key]
keys (IntMap m) =
  coerce $ Containers.keys m

elems :: IntMap key value -> [value]
elems (IntMap m) =
  Containers.elems m

mapMaybe :: (value1 -> Maybe value2) -> IntMap key value1 -> IntMap key value2
mapMaybe f (IntMap m) =
  coerce $ Containers.mapMaybe f m

mapMaybeWithKey :: Coercible key Containers.Key => (key -> value1 -> Maybe value2) -> IntMap key value1 -> IntMap key value2
mapMaybeWithKey f (IntMap m) =
  IntMap $ Containers.mapMaybeWithKey (coerce f) m

mapEither :: (value -> Either value1 value2) -> IntMap key value -> (IntMap key value1, IntMap key value2)
mapEither f (IntMap m) =
  coerce $ Containers.mapEither f m

mapEitherWithKey ::
  (Coercible key Containers.Key) =>
  (key -> value -> Either value1 value2) ->
  IntMap key value ->
  (IntMap key value1, IntMap key value2)
mapEitherWithKey f (IntMap m) =
  bimap IntMap IntMap $ Containers.mapEitherWithKey (coerce f) m

mapKeysMonotonic ::
  (Coercible key1 Containers.Key, Coercible key2 Containers.Key) =>
  (key1 -> key2) ->
  IntMap key1 value ->
  IntMap key2 value
mapKeysMonotonic f (IntMap m) =
  IntMap $ Containers.mapKeysMonotonic (coerce f) m
