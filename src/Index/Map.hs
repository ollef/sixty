{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language PackageImports #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
module Index.Map where

import Protolude hiding (Map)

import qualified "containers" Data.IntMap

import qualified Data.IntSequence as IntSeq
import Data.IntSequence (IntSeq)
import Index

newtype Map v a = Map (IntSeq a)
  deriving (Show, Foldable)

pattern Empty :: (Coercible a Data.IntMap.Key) => Map Void a
pattern Empty = Map IntSeq.Empty

pattern (:>) :: (Coercible a Data.IntMap.Key) => Map v a -> a -> Map (Succ v) a
pattern as :> a <- Map ((Map -> as) IntSeq.:> a)
  where
    Map m :> a = Map $ m IntSeq.:> a

{-# COMPLETE Empty, (:>) #-}

length :: (Coercible a Data.IntMap.Key) => Map v a -> Index (Succ v)
length (Map m) = Index $ IntSeq.length m

elemIndex :: (Coercible a Data.IntMap.Key) => a -> Map v a -> Maybe (Index v)
elemIndex a (Map m) =
  (\i -> Index $ IntSeq.length m - i - 1) <$> IntSeq.elemIndex a m

index :: (Coercible a Data.IntMap.Key) => Map v a -> Index v -> a
index (Map m) (Index i) =
  IntSeq.index m (IntSeq.length m - i - 1)
