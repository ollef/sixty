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

import qualified Data.Sequence as Seq
import qualified "containers" Data.IntMap

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil

data IntSeq a = IntSeq !(Seq a) (IntMap a Int)

instance Semigroup (IntSeq a) where
  IntSeq seq1 indices1 <> IntSeq seq2 indices2 =
    IntSeq (seq1 <> seq2) (indices1 <> map (+ Seq.length seq1) indices2)

instance Show a => Show (IntSeq a) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (toList xs)

instance Monoid (IntSeq a) where
  mempty =
    IntSeq mempty mempty

instance Foldable IntSeq where
  foldMap f (IntSeq seq _) =
    foldMap f seq

pattern Empty :: (Coercible a Data.IntMap.Key) => IntSeq a
pattern Empty <- IntSeq Seq.Empty _
  where
    Empty = mempty

pattern (:>) :: (Coercible a Data.IntMap.Key) => IntSeq a -> a -> IntSeq a
pattern as :> a <- (unsnoc -> Just (as, a))
  where
    IntSeq seq indices :> a = IntSeq (seq Seq.:|> a) (IntMap.insert a (Seq.length seq) indices)

unsnoc :: (Coercible a Data.IntMap.Key) => IntSeq a -> Maybe (IntSeq a, a)
unsnoc (IntSeq seq indices) =
  case seq of
    seq' Seq.:|> a ->
      Just (IntSeq seq' $ IntMap.delete a indices, a)

    _ -> Nothing

{-# COMPLETE Empty, (:>) #-}

length :: IntSeq a -> Int
length (IntSeq seq _) =
  Seq.length seq

singleton :: (Coercible a Data.IntMap.Key) => a -> IntSeq a
singleton a =
  Empty :> a

member :: (Coercible a Data.IntMap.Key) => a -> IntSeq a -> Bool
member a (IntSeq _ indices) =
  IntMap.member a indices

elemIndex :: (Coercible a Data.IntMap.Key) => a -> IntSeq a -> Maybe Int
elemIndex a (IntSeq _ indices) =
  IntMap.lookup a indices

index :: IntSeq a -> Int -> a
index (IntSeq seq _) =
  Seq.index seq

splitAt :: Int -> IntSeq a -> (IntSeq a, IntSeq a)
splitAt i (IntSeq seq indices) =
  (IntSeq seq1 indices1, IntSeq seq2 indices2)
  where
    (seq1, seq2) = Seq.splitAt i seq
    (indices1, indices2) = IntMap.mapEither (\j -> if j < i then Left j else Right $ j - i) indices

insertAt :: (Coercible a Data.IntMap.Key) => Int -> a -> IntSeq a -> IntSeq a
insertAt i a (IntSeq seq indices) =
  IntSeq (Seq.insertAt i a seq) (IntMap.insert a i indices')
  where
    indices' = map (\j -> if j < i then j else j + 1) indices

delete :: (Coercible a Data.IntMap.Key) => a -> IntSeq a -> IntSeq a
delete a as =
  case elemIndex a as of
    Nothing ->
      as

    Just i ->
      deleteAt i as

deleteAt :: Int -> IntSeq a -> IntSeq a
deleteAt i (IntSeq seq indices) =
  IntSeq (Seq.deleteAt i seq) indices'
  where
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
toTsil (IntSeq seq _) =
  go seq
  where
  go as =
    case as of
      Seq.Empty ->
        Tsil.Empty

      as' Seq.:|> a ->
        go as' Tsil.:> a
