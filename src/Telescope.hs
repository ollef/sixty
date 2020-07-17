{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language StandaloneDeriving #-}
module Telescope where

import Protolude

import Unsafe.Coerce
import Data.Persist

import Index
import Plicity

data Telescope name type_ base v
  = Empty !(base v)
  | Extend !name !(type_ v) !Plicity !(Scope (Telescope name type_ base) v)
  deriving (Generic)

deriving instance
  (Eq n, forall v'. Eq (t v'), forall v'. Eq (k v'))
    => Eq (Telescope n t k v)

deriving instance
  (Show n, (forall v'. Show (t v')), (forall v'. Show (k v')))
    => Show (Telescope n t k v)

deriving instance
  (Persist n, (forall v'. Persist (t v')), (forall v'. Persist (k v')))
    => Persist (Telescope n t k v)

deriving instance
  (Hashable n, (forall v'. Hashable (t v')), (forall v'. Hashable (k v')))
    => Hashable (Telescope n t k v)

hoist :: (forall v'. k v' -> k' v') -> Telescope n t k v -> Telescope n t k' v
hoist f tele =
  case tele of
    Empty k ->
      Empty $ f k

    Extend name t plicity scope ->
      Extend name t plicity $ hoist f scope

fold
  :: (forall v'. n -> t v' -> Plicity -> Scope k v' -> k v')
  -> Telescope n t k v
  -> k v
fold f tele =
  case tele of
    Empty k ->
      k

    Extend name t plicity scope ->
      f name t plicity $ Telescope.fold f scope

fromVoid :: Telescope n t k Void -> Telescope n t k v
fromVoid = unsafeCoerce

length :: Telescope n t k v -> Int
length tele =
  case tele of
    Empty _ ->
      0

    Extend _ _ _ tele' ->
      1 + Telescope.length tele'
