module Domain.Telescope where

import qualified Domain
import Monad
import Name (Name)
import Plicity

data Telescope t k
  = Empty !k
  | Extend !Name !t !Plicity (Lazy Domain.Value -> M (Telescope t k))
