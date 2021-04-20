{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Telescope where

import Data.Persist
import Index
import Plicity
import Protolude
import Unsafe.Coerce

data Telescope name type_ base v
  = Empty !(base v)
  | Extend !name !(type_ v) !Plicity !(Scope (Telescope name type_ base) v)
  deriving (Generic)

deriving instance
  (Eq n, forall v'. Eq (t v'), forall v'. Eq (k v')) =>
  Eq (Telescope n t k v)

deriving instance
  (Show n, (forall v'. Show (t v')), (forall v'. Show (k v'))) =>
  Show (Telescope n t k v)

deriving instance
  (Persist n, (forall v'. Persist (t v')), (forall v'. Persist (k v'))) =>
  Persist (Telescope n t k v)

deriving instance
  (Hashable n, (forall v'. Hashable (t v')), (forall v'. Hashable (k v'))) =>
  Hashable (Telescope n t k v)

under :: Telescope n t k v -> (forall v'. k v' -> result) -> result
under tele f =
  case tele of
    Empty k -> f k
    Extend _ _ _ tele' -> under tele' f

hoist :: (forall v'. t v' -> t' v') -> (forall v'. k v' -> k' v') -> Telescope n t k v -> Telescope n t' k' v
hoist f g tele =
  case tele of
    Empty k ->
      Empty $ g k
    Extend name t plicity scope ->
      Extend name (f t) plicity $ hoist f g scope

hoistA :: Applicative f => (forall v'. t v' -> f (t' v')) -> (forall v'. k v' -> f (k' v')) -> Telescope n t k v -> f (Telescope n t' k' v)
hoistA f g tele =
  case tele of
    Empty k ->
      Empty <$> g k
    Extend name t plicity scope ->
      Extend name <$> f t <*> pure plicity <*> hoistA f g scope

fold ::
  (forall v'. n -> t v' -> Plicity -> Scope k v' -> k v') ->
  Telescope n t k v ->
  k v
fold f =
  Telescope.foldr f identity

foldr ::
  (forall v'. n -> t v' -> Plicity -> Scope result v' -> result v') ->
  (forall v'. k v' -> result v') ->
  Telescope n t k v ->
  result v
foldr f g tele =
  case tele of
    Empty k ->
      g k
    Extend name t plicity scope ->
      f name t plicity $ Telescope.foldr f g scope

fromVoid :: Telescope n t k Void -> Telescope n t k v
fromVoid = unsafeCoerce

length :: Telescope n t k v -> Int
length tele =
  case tele of
    Empty _ ->
      0
    Extend _ _ _ tele' ->
      1 + Telescope.length tele'
