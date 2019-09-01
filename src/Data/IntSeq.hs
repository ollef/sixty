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
import Protolude hiding (IntMap)

import Data.Coerce
import Data.FingerTree (FingerTree)
import qualified Data.FingerTree as FingerTree
import qualified "containers" Data.IntMap

import "this" Data.IntMap (IntMap)
import qualified "this" Data.IntMap as IntMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil

data IndexMap a = IndexMap !Int (IntMap a Int)

instance Semigroup (IndexMap a) where
  IndexMap 0 _ <> indexMap =
    indexMap
  indexMap <> IndexMap 0 _ =
    indexMap
  IndexMap n1 m1 <> IndexMap n2 m2 =
    IndexMap (n1 + n2) (m1 <> ((+ n1) <$> m2))

instance Monoid (IndexMap a) where
  mempty = IndexMap 0 mempty

newtype IndexMapped a = IndexMapped a

instance (Coercible a Data.IntMap.Key) => FingerTree.Measured (IndexMap a) (IndexMapped a) where
  measure (IndexMapped a) = IndexMap 1 (IntMap.singleton a 0)

newtype IntSeq a = IntSeq (FingerTree (IndexMap a) (IndexMapped a))

deriving instance (Coercible a Data.IntMap.Key) => Semigroup (IntSeq a)
deriving instance (Coercible a Data.IntMap.Key) => Monoid (IntSeq a)

instance Foldable IntSeq where
  foldMap f (IntSeq ft) = foldMap (coerce f) ft

instance Show a => Show (IntSeq a) where
  showsPrec p xs = showParen (p > 10) $
    showString "fromList " . shows (toList xs)

pattern Empty :: (Coercible a Data.IntMap.Key) => IntSeq a
pattern Empty <- IntSeq (FingerTree.null -> True)
  where
    Empty = mempty

pattern (:>) :: (Coercible a Data.IntMap.Key) => IntSeq a -> a -> IntSeq a
pattern as :> a <- IntSeq (FingerTree.viewr -> (IntSeq -> as) FingerTree.:> IndexMapped a)
  where
    IntSeq ft :> a = IntSeq (ft FingerTree.|> IndexMapped a)

{-# COMPLETE Empty, (:>) #-}

singleton :: (Coercible a Data.IntMap.Key) => a -> IntSeq a
singleton a =
  Empty :> a

length :: (Coercible a Data.IntMap.Key) => IntSeq a -> Int
length (IntSeq ft) =
  let
    IndexMap len _ = FingerTree.measure ft
  in
  len

member :: (Coercible a Data.IntMap.Key) => a -> IntSeq a -> Bool
member a (IntSeq ft) =
  let
    IndexMap _ m = FingerTree.measure ft
  in
  IntMap.member a m

elemIndex :: (Coercible a Data.IntMap.Key) => a -> IntSeq a -> Maybe Int
elemIndex a (IntSeq ft) =
  let
    IndexMap _ m = FingerTree.measure ft
  in
  IntMap.lookup a m

index :: (Coercible a Data.IntMap.Key) => IntSeq a -> Int -> a
index (IntSeq ft) i =
  let
    r = FingerTree.dropUntil (\(IndexMap len _) -> len > i) ft
  in
  case FingerTree.viewl r of
    FingerTree.EmptyL ->
      panic "Sequence.index: out of bounds"

    IndexMapped a FingerTree.:< _ ->
      a

splitAt :: (Coercible a Data.IntMap.Key) => Int -> IntSeq a -> (IntSeq a, IntSeq a)
splitAt i (IntSeq ft) =
  coerce $ FingerTree.split (\(IndexMap len _) -> len > i) ft

insertAt :: (Coercible a Data.IntMap.Key) => Int -> a -> IntSeq a -> IntSeq a
insertAt i a as =
  let
    (l, r) =
      Data.IntSeq.splitAt i as

  in
  l <> singleton a <> r

delete :: (Coercible a Data.IntMap.Key) => a -> IntSeq a -> IntSeq a
delete a as =
  case elemIndex a as of
    Nothing ->
      as

    Just i ->
      deleteAt i as

deleteAt :: (Coercible a Data.IntMap.Key) => Int -> IntSeq a -> IntSeq a
deleteAt i (IntSeq ft) =
  let
    (l, r) = FingerTree.split (\(IndexMap len _) -> len > i) ft
  in
  coerce $
    case FingerTree.viewl r of
      FingerTree.EmptyL ->
        l

      _ FingerTree.:< r' ->
        l <> r'

fromTsil :: (Coercible a Data.IntMap.Key) => Tsil a -> IntSeq a
fromTsil tsil =
  case tsil of
    Tsil.Empty ->
      mempty

    as Tsil.:> a ->
      fromTsil as :> a

toTsil :: (Coercible a Data.IntMap.Key) => IntSeq a -> Tsil a
toTsil as =
  case as of
    Empty ->
      Tsil.Empty

    as' :> a ->
      toTsil as' Tsil.:> a
