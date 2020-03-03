{-# language ConstraintKinds #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language StandaloneDeriving #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Query.Mapped where

import Protolude

import Control.Monad.Fail
import Data.Constraint
import Data.Constraint.Extras
import qualified Data.Dependent.HashMap as DHashMap
import Data.GADT.Compare
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Persist as Persist
import Rock

import HashTag
import Orphans ()
import PersistTag

data Query key result a where
  Map :: Query key result (HashMap key result)
  Query :: key -> Query key result (Maybe result)

deriving instance (Show key, Show result) => Show (Query key result a)

instance (Hashable key, Hashable result) => Hashable (Query key result a) where
  hashWithSalt salt query =
    case query of
      Map ->
        hashWithSalt salt (0 :: Int)

      Query key ->
        hashWithSalt salt (1 :: Int, key)

rule
  :: (Eq key, Hashable key)
  => (forall a'. Query key result a' -> query a')
  -> Query key result a
  -> Task query (HashMap key result)
  -> Task query a
rule inject query fetchMap =
  case query of
    Map ->
      fetchMap

    Query key -> do
      m <- fetch $ inject Map
      pure $ HashMap.lookup key m

instance Eq key => GEq (Query key result) where
  geq Map Map = Just Refl
  geq (Query k1) (Query k2)
    | k1 == k2 = Just Refl
  geq _ _ = Nothing

instance (Eq key, Ord key) => GCompare (Query key result) where
  gcompare Map Map = GEQ
  gcompare Map _ = GLT
  gcompare _ Map = GGT
  gcompare (Query k1) (Query k2) =
    case compare k1 k2 of
      LT -> GLT
      EQ -> GEQ
      GT -> GGT

instance ArgDict c (Query key result) where
  type ConstraintsFor (Query key result) c = (c (HashMap key result), c (Maybe result))
  argDict query =
    case query of
      Map -> Dict
      Query {} -> Dict

instance (Hashable key, Hashable result) => HashTag (Query key result) where
  hashTagged query =
    case query of
      Map {} -> hash
      Query {} -> hash

instance (Eq key, Hashable key, Persist key, Persist result, forall a. Persist a => Persist (f a)) => PersistTag (Query key result) f where
  putTagged query =
    case query of
      Map ->
        Persist.put

      Query _ ->
        Persist.put

  getTagged query =
    case query of
      Map ->
        Persist.get

      Query _ ->
        Persist.get

instance Persist key => Persist (DHashMap.Some (Query key result)) where
  put (DHashMap.Some query) =
    case query of
      Map ->
        Persist.put @Word8 0

      Query q -> do
        Persist.put @Word8 1
        Persist.put q

  get = do
    tag <- Persist.get @Word8
    case tag of
      0 ->
        pure $ DHashMap.Some Map

      1 ->
        DHashMap.Some . Query <$> Persist.get

      _ ->
        fail "getSome Query"
