{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language StandaloneDeriving #-}
module Syntax.Telescope where

import Protolude

import Unsafe.Coerce

import Index
import Name (Name)
import Plicity

data Telescope t k v
  = Empty !(k v)
  | Extend !Name !(t v) !Plicity !(Scope (Telescope t k) v)
  deriving (Generic)

deriving instance
  ((forall v'. Show (t v')), (forall v'. Show (k v')))
    => Show (Telescope t k v)

deriving instance
  ((forall v'. Hashable (t v')), (forall v'. Hashable (k v')))
    => Hashable (Telescope t k v)

hoist :: (forall v'. k v' -> k' v') -> Telescope t k v -> Telescope t k' v
hoist f tele =
  case tele of
    Empty k ->
      Empty $ f k

    Extend name t plicity scope ->
      Extend name t plicity $ hoist f scope

fold
  :: (forall v'. Name -> t v' -> Plicity -> Scope k v' -> k v')
  -> Telescope t k v
  -> k v
fold f tele =
  case tele of
    Empty k ->
      k

    Extend name t plicity scope ->
      f name t plicity $ Syntax.Telescope.fold f scope

fromVoid :: Telescope t k Void -> Telescope t k v
fromVoid = unsafeCoerce

length :: Telescope t k v -> Int
length tele =
  case tele of
    Empty _ ->
      0

    Extend _ _ _ tele' ->
      1 + Syntax.Telescope.length tele'
