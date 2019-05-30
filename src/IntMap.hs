{-# language DeriveTraversable #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
module IntMap where

import Protolude hiding (IntMap)

import qualified Data.IntMap.Lazy as Data.IntMap
import Data.Coerce

newtype IntMap key value = IntMap (Data.IntMap.IntMap value)
  deriving (Functor, Foldable, Traversable, Eq, Ord, Read, Show, Semigroup, Monoid)

instance (Hashable key, Hashable value, Coercible Data.IntMap.Key key) => Hashable (IntMap key value) where
  hashWithSalt salt (IntMap m) = hashWithSalt salt (coerce $ Data.IntMap.toList m :: [(key, value)])

null :: IntMap key value -> Bool
null (IntMap m) = Data.IntMap.null m

singleton :: Coercible key Data.IntMap.Key => key -> value -> IntMap key value
singleton key value = IntMap $ Data.IntMap.singleton (coerce key) value

fromList :: Coercible key Data.IntMap.Key => [(key, value)] -> IntMap key value
fromList xs = IntMap $ Data.IntMap.fromList $ coerce xs

toList :: Coercible key Data.IntMap.Key => IntMap key value -> [(key, value)]
toList (IntMap m) = coerce $ Data.IntMap.toList m

insert :: Coercible key Data.IntMap.Key => key -> value -> IntMap key value -> IntMap key value
insert key value = coerce $ Data.IntMap.insert (coerce key) value

adjust :: Coercible key Data.IntMap.Key => (value -> value) -> key -> IntMap key value -> IntMap key value
adjust f key = coerce $ Data.IntMap.adjust f (coerce key)

lookup :: Coercible key Data.IntMap.Key => key -> IntMap key value -> Maybe value
lookup key m = Data.IntMap.lookup (coerce key) (coerce m)

(!) :: Coercible key Data.IntMap.Key => IntMap key value -> key -> value
m ! key = coerce m Data.IntMap.! coerce key

lookupDefault :: Coercible key Data.IntMap.Key => value -> key -> IntMap key value -> value
lookupDefault def key m = Data.IntMap.findWithDefault def (coerce key) (coerce m)

member :: Coercible key Data.IntMap.Key => key -> IntMap key value -> Bool
member key (IntMap m) = Data.IntMap.member (coerce key) m

unionWith :: (value -> value -> value) -> IntMap key value -> IntMap key value -> IntMap key value
unionWith f m1 m2 = IntMap $ Data.IntMap.unionWith f (coerce m1) (coerce m2)

traverseWithKey :: (Coercible key Data.IntMap.Key, Applicative t) => (key -> value1 -> t value2) -> IntMap key value1 -> t (IntMap key value2)
traverseWithKey f (IntMap m) = IntMap <$> Data.IntMap.traverseWithKey (coerce f) m

