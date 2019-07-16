{-# language GADTs #-}
module Data.Some where

data Some k where
  Some :: k v -> Some k
