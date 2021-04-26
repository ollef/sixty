{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Data.IntSeq where

import Data.Coerce
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Protolude hiding (IntMap, seq, splitAt, unsnoc)
import Prelude (Show (showsPrec), showParen, showString, shows)

data IntSeq a
  = Empty
  | Snoc (IntSeq a) !Int !Int
  deriving (Eq)

instance Semigroup (IntSeq a) where
  as <> Empty = as
  as <> Snoc outerBs outerValue2 outerCount2 =
    go outerBs outerValue2 outerCount2
    where
      go bs value2 count2 =
        case bs of
          Empty ->
            snocNonZeroCount as value2 count2
          Snoc bs' value2' count2' ->
            Snoc (go bs' value2' count2') value2 count2

instance (Coercible a Int, Show a) => Show (IntSeq a) where
  showsPrec p xs =
    showParen (p > 10) $
      showString "fromList " . shows (Data.IntSeq.toList xs)

instance Monoid (IntSeq a) where
  mempty = Empty

pattern (:>) :: Coercible a Int => IntSeq a -> a -> IntSeq a
pattern as :> a <-
  (unsnoc -> Just (as, a))
  where
    (:>) = snoc

{-# COMPLETE Empty, (:>) #-}

unsnoc :: Coercible a Int => IntSeq a -> Maybe (IntSeq a, a)
unsnoc Empty = Nothing
unsnoc (Snoc as a 1) = Just (as, coerce a)
unsnoc (Snoc as a n) = Just (Snoc as a (n - 1), coerce $ coerce a + n - 1)

snoc :: Coercible a Int => IntSeq a -> a -> IntSeq a
snoc s a = snocNonZeroCount s (coerce a) 1

-- TODO: Make internal
snocCount :: IntSeq a -> Int -> Int -> IntSeq a
snocCount as _ 0 = as
snocCount as a n = snocNonZeroCount as a n

-- TODO: Make internal
snocNonZeroCount :: IntSeq a -> Int -> Int -> IntSeq a
snocNonZeroCount Empty a count = Snoc Empty a count
snocNonZeroCount as@(Snoc as' a' count') a count
  | a' + count' == a = Snoc as' a' (count' + count)
  | otherwise = Snoc as a count

length :: IntSeq a -> Int
length Empty = 0
length (Snoc as _ count) = Data.IntSeq.length as + count

singleton :: Coercible a Int => a -> IntSeq a
singleton a = Empty :> a

member :: Coercible a Int => a -> IntSeq a -> Bool
member _ Empty = False
member a (Snoc as a' count)
  | ca <- coerce a
    , a' <= ca
    , ca < a' + count =
    True
  | otherwise = member a as

elemIndex :: Coercible a Int => a -> IntSeq a -> Maybe Int
elemIndex _ Empty = Nothing
elemIndex a (Snoc as a' count)
  | ca <- coerce a
    , a' <= ca
    , ca < a' + count =
    Just $ a' + count - ca - 1
  | otherwise = (+ count) <$> elemIndex a as

index :: Coercible a Int => IntSeq a -> Int -> a
index Empty _ = panic "Data.IntSeq.index: out of bounds"
index (Snoc as a count) i
  | i < count = coerce $ a + count - i - 1
  | otherwise = index as $ i - count

insertAt :: Coercible a Int => Int -> a -> IntSeq a -> IntSeq a
insertAt _ a Empty = singleton a
insertAt i a (Snoc as a' count)
  | i < count =
    snocCount
      ( snocNonZeroCount
          (snocCount as a' (count - i))
          (coerce a)
          1
      )
      (a' + count - i)
      i
  | otherwise = snocNonZeroCount (insertAt (i - count) a as) a' count

deleteFirst :: Coercible a Int => a -> IntSeq a -> IntSeq a
deleteFirst _ Empty = Empty
deleteFirst a (Snoc as a' count)
  | ca <- coerce a
    , a' <= ca
    , ca < a' + count = do
    let prefixCount = ca - a'
        suffixCount = count - prefixCount - 1
    snocCount (snocCount as a' prefixCount) (ca + 1) suffixCount
  | otherwise = do
    snocNonZeroCount (deleteFirst a as) a' count

delete :: Coercible a Int => a -> IntSeq a -> IntSeq a
delete _ Empty = Empty
delete a (Snoc as a' count)
  | ca <- coerce a
    , a' <= ca
    , ca < a' + count = do
    let prefixCount = ca - a'
        suffixCount = count - prefixCount - 1
    snocCount (snocCount (delete a as) a' prefixCount) (ca + 1) suffixCount
  | otherwise = do
    snocNonZeroCount (deleteFirst a as) a' count

fromList :: Coercible a Int => [a] -> IntSeq a
fromList = go Empty
  where
    go acc [] = acc
    go acc (a : as) = go (acc :> a) as

toList :: Coercible a Int => IntSeq a -> [a]
toList = go []
  where
    go acc Empty = acc
    go acc (as :> a) = go (a : acc) as

fromTsil :: Coercible a Int => Tsil a -> IntSeq a
fromTsil Tsil.Empty = Empty
fromTsil (as Tsil.:> a) = fromTsil as :> a

toTsil :: Coercible a Int => IntSeq a -> Tsil a
toTsil Empty = Tsil.Empty
toTsil (as :> a) = toTsil as Tsil.:> a
