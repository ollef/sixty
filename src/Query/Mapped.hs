{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Query.Mapped where

import Data.Constraint
import Data.Constraint.Extras
import Data.GADT.Compare
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Orphans ()
import Protolude
import Rock

data Query key result a where
  Map :: Query key result (HashMap key result)
  Query :: key -> Query key result (Maybe result)

deriving instance (Show key, Show result) => Show (Query key result a)

deriving instance (Eq key, Eq result) => Eq (Query key result a)

instance (Hashable key, Hashable result) => Hashable (Query key result a) where
  hashWithSalt salt query =
    case query of
      Map ->
        hashWithSalt salt (0 :: Int)
      Query key ->
        hashWithSalt salt (1 :: Int, key)

rule
  :: (Hashable key)
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

instance (Eq key) => GEq (Query key result) where
  geq Map Map = Just Refl
  geq (Query k1) (Query k2)
    | k1 == k2 = Just Refl
  geq _ _ = Nothing

instance (Ord key) => GCompare (Query key result) where
  gcompare Map Map = GEQ
  gcompare Map _ = GLT
  gcompare _ Map = GGT
  gcompare (Query k1) (Query k2) =
    case compare k1 k2 of
      LT -> GLT
      EQ -> GEQ
      GT -> GGT

instance (c (Maybe result), c (HashMap key result)) => Has c (Query key result) where
  argDict query =
    case query of
      Map -> Dict
      Query {} -> Dict
