module Orphans where

import Protolude

import Data.Vector (Vector)
import qualified Data.Vector as Vector

instance Hashable a => Hashable (Vector a) where
  hashWithSalt salt = hashWithSalt salt . Vector.toList
