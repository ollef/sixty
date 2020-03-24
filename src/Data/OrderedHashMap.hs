{-# language DeriveFoldable #-}
{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}
module Data.OrderedHashMap where

import Prelude (Show(showsPrec), showParen, showString, shows)
import Protolude hiding (toList, get, put)

import Data.HashMap.Lazy (HashMap)
import Data.Persist
import qualified Data.HashMap.Lazy as HashMap

newtype OrderedHashMap k v = OrderedHashMap { toMap :: HashMap k (Ordered v) }
  deriving (Functor)

instance (Eq k, Eq v) => Eq (OrderedHashMap k v) where
  (==) =
    (==) `on` toList

instance (Ord k, Ord v) => Ord (OrderedHashMap k v) where
  compare =
    compare `on` toList

instance (Show k, Show v) => Show (OrderedHashMap k v) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (toList xs)

instance Foldable (OrderedHashMap k) where
  foldMap f (OrderedHashMap h) =
    foldMap (\(Ordered _ v) -> f v) $
    sortBy (comparing $ \(Ordered n _) -> n) $
    HashMap.elems h

instance (Hashable k, Hashable v) => Hashable (OrderedHashMap k v) where
  hashWithSalt s =
    hashWithSalt s . toList

instance (Eq k, Hashable k, Persist k, Persist v) => Persist (OrderedHashMap k v) where
  get =
    fromList <$> get

  put =
    put . toList

null :: OrderedHashMap k v -> Bool
null (OrderedHashMap h) =
  HashMap.null h

size :: OrderedHashMap k v -> Int
size (OrderedHashMap h) =
  HashMap.size h

lookup :: (Eq k, Hashable k) => k -> OrderedHashMap k v -> Maybe v
lookup k (OrderedHashMap h) =
  (\(Ordered _ v) -> v) <$> HashMap.lookup k h

lookupDefault :: (Eq k, Hashable k) => v -> k -> OrderedHashMap k v -> v
lookupDefault def k (OrderedHashMap h) =
  (\(Ordered _ v) -> v) $ HashMap.lookupDefault (Ordered 0 def) k h

mapMUnordered :: Applicative f => (a -> f b) -> OrderedHashMap k a -> f (OrderedHashMap k b)
mapMUnordered f (OrderedHashMap h) =
  OrderedHashMap <$> traverse (traverse f) h

forMUnordered :: Applicative f => OrderedHashMap k a -> (a -> f b) -> f (OrderedHashMap k b)
forMUnordered =
  flip mapMUnordered

data Ordered v = Ordered !Int v
  deriving (Functor, Foldable, Traversable)

keys :: OrderedHashMap k v -> [k]
keys =
  map fst . toList

elems :: OrderedHashMap k v -> [v]
elems =
  map snd . toList

toList :: OrderedHashMap k v -> [(k, v)]
toList (OrderedHashMap h) =
  map (\(k, Ordered _ v) -> (k, v)) $
  sortBy (comparing $ \(_, Ordered n _) -> n) $
  HashMap.toList h

fromList
  :: (Eq k, Hashable k)
  => [(k, v)]
  -> OrderedHashMap k v
fromList =
  OrderedHashMap .
  HashMap.fromList .
  zipWith (\n (k, v) -> (k, Ordered n v)) [0..]

fromListWith
  :: (Eq k, Hashable k)
  => (v -> v -> v)
  -> [(k, v)]
  -> OrderedHashMap k v
fromListWith f =
  OrderedHashMap .
  HashMap.fromListWith (\(Ordered i v1) (Ordered _ v2) -> Ordered i $ f v1 v2) .
  zipWith (\n (k, v) -> (k, Ordered n v)) [0..]

intersectionWith
  :: (Eq k, Hashable k)
  => (v1 -> v2 -> v3)
  -> OrderedHashMap k v1
  -> OrderedHashMap k v2
  -> OrderedHashMap k v3
intersectionWith f (OrderedHashMap h1) (OrderedHashMap h2) =
  OrderedHashMap $
    HashMap.intersectionWith
      (\(Ordered i v1) (Ordered _ v2) -> Ordered i $ f v1 v2)
      h1
      h2

difference :: (Eq k, Hashable k) => OrderedHashMap k v -> OrderedHashMap k w -> OrderedHashMap k v
difference (OrderedHashMap h1) (OrderedHashMap h2) =
  OrderedHashMap $
    HashMap.difference h1 h2

differenceFromMap :: (Eq k, Hashable k) => OrderedHashMap k v -> HashMap k w -> OrderedHashMap k v
differenceFromMap (OrderedHashMap h1) h2 =
  OrderedHashMap $
    HashMap.difference h1 h2
