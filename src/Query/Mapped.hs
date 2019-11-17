{-# language GADTs #-}
{-# language RankNTypes #-}
{-# language StandaloneDeriving #-}
module Query.Mapped where

import Protolude

import Data.GADT.Compare
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Rock

data Query key result a where
  Map :: Query key result (HashMap key result)
  Query :: key -> Query key result (Maybe result)

deriving instance (Show key, Show result) => Show (Query key result a)

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

errorRule
  :: (Eq key, Hashable key, Monoid error)
  => (forall a'. Query key result a' -> query a')
  -> Query key result a
  -> Task query (HashMap key result, error)
  -> Task query (a, error)
errorRule inject query fetchMap =
  case query of
    Map ->
      fetchMap

    Query key -> do
      m <- fetch $ inject Map
      pure (HashMap.lookup key m, mempty)

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

instance (Hashable key, Hashable result) => HashTag (Query key result) where
  hashTagged query =
    case query of
      Map {} -> hash
      Query {} -> hash
