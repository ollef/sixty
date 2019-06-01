{-# language DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language PackageImports #-}
{-# language ScopedTypeVariables #-}
module Data.IntMap where

import Protolude hiding (IntMap)

import Data.Coerce
import qualified "containers" Data.IntMap.Lazy as Containers

newtype IntMap key value = IntMap (Containers.IntMap value)
  deriving (Functor, Foldable, Traversable, Eq, Ord, Read, Show, Semigroup, Monoid)

instance (Hashable key, Hashable value, Coercible Containers.Key key) => Hashable (IntMap key value) where
  hashWithSalt salt (IntMap m) = hashWithSalt salt (coerce $ Containers.toList m :: [(key, value)])

null :: IntMap key value -> Bool
null (IntMap m) = Containers.null m

singleton :: Coercible key Containers.Key => key -> value -> IntMap key value
singleton key value = IntMap $ Containers.singleton (coerce key) value

fromList :: Coercible key Containers.Key => [(key, value)] -> IntMap key value
fromList xs = IntMap $ Containers.fromList $ coerce xs

toList :: Coercible key Containers.Key => IntMap key value -> [(key, value)]
toList (IntMap m) = coerce $ Containers.toList m

insert :: Coercible key Containers.Key => key -> value -> IntMap key value -> IntMap key value
insert key value = coerce $ Containers.insert (coerce key) value

adjust :: Coercible key Containers.Key => (value -> value) -> key -> IntMap key value -> IntMap key value
adjust f key = coerce $ Containers.adjust f (coerce key)

lookup :: Coercible key Containers.Key => key -> IntMap key value -> Maybe value
lookup key m = Containers.lookup (coerce key) (coerce m)

(!) :: Coercible key Containers.Key => IntMap key value -> key -> value
m ! key = coerce m Containers.! coerce key

lookupDefault :: Coercible key Containers.Key => value -> key -> IntMap key value -> value
lookupDefault def key m = Containers.findWithDefault def (coerce key) (coerce m)

member :: Coercible key Containers.Key => key -> IntMap key value -> Bool
member key (IntMap m) = Containers.member (coerce key) m

unionWith :: (value -> value -> value) -> IntMap key value -> IntMap key value -> IntMap key value
unionWith f m1 m2 = IntMap $ Containers.unionWith f (coerce m1) (coerce m2)

traverseWithKey :: (Coercible key Containers.Key, Applicative t) => (key -> value1 -> t value2) -> IntMap key value1 -> t (IntMap key value2)
traverseWithKey f (IntMap m) = IntMap <$> Containers.traverseWithKey (coerce f) m

