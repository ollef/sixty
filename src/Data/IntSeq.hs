{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language PatternSynonyms #-}
{-# language StandaloneDeriving #-}
{-# language ViewPatterns #-}
module Data.IntSeq where

import Prelude (Show(showsPrec), showParen, showString, shows)
import Protolude hiding (IntMap, unsnoc, seq, splitAt)

import qualified "containers" Data.IntMap

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil

data IntSeq a = IntSeq !Int (IntMap Int a) (IntMap a Int)

instance Semigroup (IntSeq a) where
  IntSeq length1 values1 indices1 <> IntSeq length2 values2 indices2 =
    IntSeq (length1 + length2) (values1 <> IntMap.mapKeysMonotonic (+ length1) values2) (indices1 <> map (+ length1) indices2)

instance Show a => Show (IntSeq a) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (toList xs)

instance Monoid (IntSeq a) where
  mempty =
    IntSeq 0 mempty mempty

instance Foldable IntSeq where
  foldMap f =
    foldMap f . toList

pattern Empty :: (Coercible a Data.IntMap.Key) => IntSeq a
pattern Empty <- IntSeq 0 _ _
  where
    Empty = mempty

pattern (:>) :: (Coercible a Data.IntMap.Key) => IntSeq a -> a -> IntSeq a
pattern as :> a <- (unsnoc -> Just (as, a))
  where
    IntSeq length_ values indices :> a = IntSeq (length_ + 1) (IntMap.insert length_ a values) (IntMap.insert a length_ indices)

unsnoc :: (Coercible a Data.IntMap.Key) => IntSeq a -> Maybe (IntSeq a, a)
unsnoc (IntSeq length_ values indices) =
  case length_ of
    0 ->
      Nothing

    _ -> do
      let
        (a, values') =
          IntMap.alterF alter (length_ - 1) values

        indices' =
          IntMap.delete a indices
      Just (IntSeq (length_ - 1) values' indices', a)
  where
    alter Nothing =
      panic "Data.IntSeq.unsnoc"

    alter (Just a) =
      (a, Nothing)

{-# COMPLETE Empty, (:>) #-}

length :: IntSeq a -> Int
length (IntSeq length_ _ _) =
  length_

singleton :: (Coercible a Data.IntMap.Key) => a -> IntSeq a
singleton a =
  Empty :> a

member :: (Coercible a Data.IntMap.Key) => a -> IntSeq a -> Bool
member a (IntSeq _ _ indices) =
  IntMap.member a indices

elemIndex :: (Coercible a Data.IntMap.Key) => a -> IntSeq a -> Maybe Int
elemIndex a (IntSeq _ _ indices) =
  IntMap.lookup a indices

index :: IntSeq a -> Int -> a
index (IntSeq _ values _) i =
  values IntMap.! i

splitAt :: Int -> IntSeq a -> (IntSeq a, IntSeq a)
splitAt i (IntSeq length_ values indices) =
  (IntSeq i values1 indices1, IntSeq (length_ - i) values2' indices2)
  where
    (values1, values2) = IntMap.mapEitherWithKey (\j -> if j < i then Left else Right) values
    values2' = IntMap.mapKeysMonotonic (subtract i) values2
    (indices1, indices2) = IntMap.mapEither (\j -> if j < i then Left j else Right $ j - i) indices

insertAt :: (Coercible a Data.IntMap.Key) => Int -> a -> IntSeq a -> IntSeq a
insertAt i a (IntSeq length_ values indices) =
  IntSeq (length_ + 1) (IntMap.insert i a values') (IntMap.insert a i indices')
  where
    values' = IntMap.mapKeysMonotonic (\j-> if j < i then j else j + 1) values
    indices' = map (\j -> if j < i then j else j + 1) indices

delete :: (Coercible a Data.IntMap.Key) => a -> IntSeq a -> IntSeq a
delete a as =
  case elemIndex a as of
    Nothing ->
      as

    Just i ->
      deleteAt i as

deleteAt :: Int -> IntSeq a -> IntSeq a
deleteAt i (IntSeq length_ values indices) =
  IntSeq (length_ - 1) values' indices'
  where
    values' =
      IntMap.mapKeysMonotonic (\j -> if j < i then j else j - 1) $
      IntMap.delete i values

    indices' =
      IntMap.mapMaybe
        (\j ->
          case compare j i of
            LT ->
              Just j

            EQ ->
              Nothing

            GT ->
              Just $ j - 1
        )
        indices

fromTsil :: (Coercible a Data.IntMap.Key) => Tsil a -> IntSeq a
fromTsil tsil =
  case tsil of
    Tsil.Empty ->
      mempty

    as Tsil.:> a ->
      fromTsil as :> a

toTsil :: IntSeq a -> Tsil a
toTsil (IntSeq _ values _) =
  Tsil.reverseFromList $ snd <$> IntMap.toDescList values
