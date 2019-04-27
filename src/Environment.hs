{-# language GADTs #-}
{-# language OverloadedStrings #-}
module Environment where

import Protolude

import qualified Bound.Var as Bound

import Index

data Environment v val where
  Nil :: Environment Void val
  Snoc :: Environment v val -> val -> Environment (Bound.Var () v) val

lookup :: Environment v val -> Index v -> val
lookup Nil v = absurdIndex v
lookup (Snoc _ val) Zero = val
lookup (Snoc env _) (Succ v) = lookup env v
lookup _ _ = panic "lookupValue"
