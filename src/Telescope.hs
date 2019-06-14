{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language StandaloneDeriving #-}
module Telescope where

import Protolude

import Index
import Name (Name)

data Telescope t k v
  = Empty (k v)
  | Extend Name (t v) (Scope (Telescope t k) v)
  deriving (Generic)

deriving instance
  ((forall v'. Show (t v')), (forall v'. Show (k v')))
    => Show (Telescope t k v)

deriving instance
  ((forall v'. Hashable (t v')), (forall v'. Hashable (k v')))
    => Hashable (Telescope t k v)
