{-# language MultiParamTypeClasses #-}
{-# language TypeOperators #-}
module PersistTag where

import Data.Persist as Persist

class PersistTag k f where
  putTagged :: k a -> f a -> Put ()
  getTagged :: k a -> Get (f a)
