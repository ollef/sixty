{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

module Index.Map where

import Data.IntSeq (IntSeq)
import qualified Data.IntSeq as IntSeq
import Data.Tsil (Tsil)
import Index
import Protolude hiding (Map)

newtype Map v a = Map (IntSeq a)

deriving instance (Coercible a Int, Show a) => Show (Map v a)

pattern Empty :: Map Void a
pattern Empty = Map IntSeq.Empty

pattern (:>) :: Coercible a Int => Map v a -> a -> Map (Succ v) a
pattern as :> a <-
  Map ((Map -> as) IntSeq.:> a)
  where
    Map m :> a = Map $ m IntSeq.:> a

{-# COMPLETE Empty, (:>) #-}

length :: Map v a -> Index (Succ v)
length (Map m) = Index $ IntSeq.length m

elemIndex :: Coercible a Int => a -> Map v a -> Maybe (Index v)
elemIndex a (Map m) =
  Index <$> IntSeq.elemIndex a m

index :: Coercible a Int => Map v a -> Index v -> a
index (Map m) (Index i) =
  IntSeq.index m i

toTsil :: Coercible a Int => Map v a -> Tsil a
toTsil (Map s) = IntSeq.toTsil s

toList :: Coercible a Int => Map v a -> [a]
toList (Map s) = IntSeq.toList s
