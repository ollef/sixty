{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Index.Seq where

import qualified Data.Sequence as Seq
import Index
import Protolude hiding (Seq)

newtype Seq v a = Seq {toSeq :: Seq.Seq a}
  deriving (Show, Foldable)

pattern Empty :: Seq Void a
pattern Empty <- Seq (Seq.null -> True)
  where
    Empty = Seq mempty

pattern (:>) :: Seq v a -> a -> Seq (Succ v) a
pattern as :> a <-
  Seq ((Seq -> as) Seq.:|> a)
  where
    Seq m :> a = Seq $ m Seq.:|> a

{-# COMPLETE Empty, (:>) #-}

length :: Seq v a -> Index (Succ v)
length (Seq m) = Index $ Seq.length m

index :: Seq v a -> Index v -> a
index (Seq m) (Index i) =
  Seq.index m (Seq.length m - i - 1)
