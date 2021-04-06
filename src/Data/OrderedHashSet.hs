{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}

module Data.OrderedHashSet where

import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Persist
import Protolude hiding (toList)
import Prelude (Show (showsPrec), showParen, showString, shows)

newtype OrderedHashSet a = OrderedHashSet (OrderedHashMap a ())
  deriving (Eq, Ord, Hashable, Persist)

instance Show a => Show (OrderedHashSet a) where
  showsPrec p xs =
    showParen (p > 10) $
      showString "fromList " . shows (toList xs)

instance Foldable OrderedHashSet where
  foldMap f =
    foldMap f . toList

null :: OrderedHashSet a -> Bool
null (OrderedHashSet s) =
  OrderedHashMap.null s

size :: OrderedHashSet a -> Int
size (OrderedHashSet s) =
  OrderedHashMap.size s

member :: (Eq a, Hashable a) => a -> OrderedHashSet a -> Bool
member a (OrderedHashSet s) =
  isJust $ OrderedHashMap.lookup a s

toList :: OrderedHashSet a -> [a]
toList (OrderedHashSet s) =
  fst <$> OrderedHashMap.toList s

fromList :: (Eq a, Hashable a) => [a] -> OrderedHashSet a
fromList as =
  OrderedHashSet $ OrderedHashMap.fromList $ (,()) <$> as
