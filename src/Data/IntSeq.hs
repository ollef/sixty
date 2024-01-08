{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Data.IntSeq where

import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import qualified Data.Sequence as Seq
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Protolude hiding (seq, splitAt, unsnoc)
import Prelude (Show (showsPrec), showParen, showString, shows)

data IntSeq a = IntSeq !(Seq a) (EnumMap a Int)

instance Semigroup (IntSeq a) where
  IntSeq seq1 indices1 <> IntSeq seq2 indices2 =
    IntSeq (seq1 <> seq2) (indices1 <> map (+ Seq.length seq1) indices2)

instance Show a => Show (IntSeq a) where
  showsPrec p xs =
    showParen (p > 10) $
      showString "fromList " . shows (toList xs)

instance Monoid (IntSeq a) where
  mempty =
    IntSeq mempty mempty

instance Foldable IntSeq where
  foldMap f (IntSeq seq _) =
    foldMap f seq

pattern Empty :: Enum a => IntSeq a
pattern Empty <-
  IntSeq Seq.Empty _
  where
    Empty = mempty

pattern (:>) :: Enum a => IntSeq a -> a -> IntSeq a
pattern as :> a <-
  (unsnoc -> Just (as, a))
  where
    IntSeq seq indices :> a = IntSeq (seq Seq.:|> a) (EnumMap.insert a (Seq.length seq) indices)

unsnoc :: Enum a => IntSeq a -> Maybe (IntSeq a, a)
unsnoc (IntSeq seq indices) =
  case seq of
    seq' Seq.:|> a ->
      Just (IntSeq seq' $ EnumMap.delete a indices, a)
    _ -> Nothing

{-# COMPLETE Empty, (:>) #-}

length :: IntSeq a -> Int
length (IntSeq seq _) =
  Seq.length seq

singleton :: Enum a => a -> IntSeq a
singleton a =
  Empty :> a

member :: Enum a => a -> IntSeq a -> Bool
member a (IntSeq _ indices) =
  EnumMap.member a indices

elemIndex :: Enum a => a -> IntSeq a -> Maybe Int
elemIndex a (IntSeq _ indices) =
  EnumMap.lookup a indices

index :: IntSeq a -> Int -> a
index (IntSeq seq _) =
  Seq.index seq

splitAt :: Int -> IntSeq a -> (IntSeq a, IntSeq a)
splitAt i (IntSeq seq indices) =
  (IntSeq seq1 indices1, IntSeq seq2 indices2)
  where
    (seq1, seq2) = Seq.splitAt i seq
    (indices1, indices2) = EnumMap.mapEither (\j -> if j < i then Left j else Right $ j - i) indices

insertAt :: Enum a => Int -> a -> IntSeq a -> IntSeq a
insertAt i a (IntSeq seq indices) =
  IntSeq (Seq.insertAt i a seq) (EnumMap.insert a i indices')
  where
    indices' = map (\j -> if j < i then j else j + 1) indices

delete :: Enum a => a -> IntSeq a -> IntSeq a
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
      EnumMap.mapMaybe
        ( \j ->
            case compare j i of
              LT ->
                Just j
              EQ ->
                Nothing
              GT ->
                Just $ j - 1
        )
        indices

fromTsil :: Enum a => Tsil a -> IntSeq a
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

toSeq :: IntSeq a -> Seq a
toSeq (IntSeq seq _) = seq

fromSeq :: Enum a => Seq a -> IntSeq a
fromSeq seq = IntSeq seq $ EnumMap.fromList $ zip (toList seq) [0 ..]
