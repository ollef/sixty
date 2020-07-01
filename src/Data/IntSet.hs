{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language PackageImports #-}
{-# language ScopedTypeVariables #-}
module Data.IntSet where

import Protolude hiding (IntSet)

import Data.Coerce
import qualified "containers" Data.IntSet as Containers

newtype IntSet key = IntSet Containers.IntSet
  deriving (Eq, Ord, Read, Show, Semigroup, Monoid)

instance (Coercible Containers.Key key, Hashable key) => Hashable (IntSet key) where
  hashWithSalt salt (IntSet s) =
    hashWithSalt salt (coerce $ Containers.toList s :: [key])

null :: IntSet key -> Bool
null (IntSet s) =
  Containers.null s

size :: IntSet key -> Int
size (IntSet s) =
  Containers.size s

singleton :: Coercible key Containers.Key => key -> IntSet key
singleton key =
  IntSet $ Containers.singleton $ coerce key

fromList :: Coercible key Containers.Key => [key] -> IntSet key
fromList xs =
  IntSet $ Containers.fromList $ coerce xs

toList :: Coercible key Containers.Key => IntSet key -> [key]
toList (IntSet s) =
  coerce $ Containers.toList s

insert :: Coercible key Containers.Key => key -> IntSet key -> IntSet key
insert key =
  coerce $ Containers.insert $ coerce key

delete :: Coercible key Containers.Key => key -> IntSet key -> IntSet key 
delete key =
  coerce $ Containers.delete $ coerce key

member :: Coercible key Containers.Key => key -> IntSet key -> Bool
member key (IntSet s) =
  Containers.member (coerce key) s

map :: (Coercible key Containers.Key, Coercible key' Containers.Key) => (key -> key') -> IntSet key -> IntSet key'
map f (IntSet s) = coerce $ Containers.map (coerce f) s

difference :: IntSet key -> IntSet key' -> IntSet key
difference (IntSet s) (IntSet t) = coerce $ Containers.difference s t

intersection :: IntSet key -> IntSet key' -> IntSet key
intersection (IntSet s) (IntSet t) = coerce $ Containers.intersection s t
