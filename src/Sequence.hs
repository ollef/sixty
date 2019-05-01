{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
module Sequence where

import Protolude hiding (Seq)

import Data.Coerce

import Data.FingerTree (FingerTree)
import qualified Data.FingerTree as FingerTree
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

data IndexMap a = IndexMap !Int (HashMap a Int)

instance (Eq a, Hashable a) => Semigroup (IndexMap a) where
  IndexMap 0 _ <> indexMap =
    indexMap
  indexMap <> IndexMap 0 _ =
    indexMap
  IndexMap n1 m1 <> IndexMap n2 m2 =
    IndexMap (n1 + n2) (m1 <> ((+ n1) <$> m2))

instance (Eq a, Hashable a) => Monoid (IndexMap a) where
  mempty = IndexMap 0 mempty

newtype IndexMapped a = IndexMapped a

instance (Eq a, Hashable a) => FingerTree.Measured (IndexMap a) (IndexMapped a) where
  measure (IndexMapped a) = IndexMap 1 (HashMap.singleton a 0)

newtype Seq a = Seq (FingerTree (IndexMap a) (IndexMapped a))
  deriving (Semigroup, Monoid)

instance Foldable Seq where
  foldMap f (Seq ft) = foldMap (coerce f) ft

(|>) :: (Eq a, Hashable a) => Seq a -> a -> Seq a
Seq ft |> a = Seq (ft FingerTree.|> IndexMapped a)

length :: (Eq a, Hashable a) => Seq a -> Int
length (Seq ft) =
  let
    IndexMap len _ = FingerTree.measure ft
  in
  len

elemIndex :: (Eq a, Hashable a) => a -> Seq a -> Maybe Int
elemIndex a (Seq ft) =
  let
    IndexMap _ m = FingerTree.measure ft
  in
  HashMap.lookup a m

index :: (Eq a, Hashable a) => Seq a -> Int -> a
index (Seq ft) i =
  let
    r = FingerTree.dropUntil (\(IndexMap len _) -> len > i) ft
  in
  case FingerTree.viewl r of
    FingerTree.EmptyL ->
      panic "Sequence.index: out of bounds"

    IndexMapped a FingerTree.:< _ ->
      a
