{-# language GADTs #-}
{-# language OverloadedStrings #-}
module Environment where

import Protolude

import Index

data Environment v val where
  Nil :: Environment Void val
  Snoc :: Environment v val -> val -> Environment (Succ v) val

lookup :: Environment v val -> Index v -> val
lookup Nil v = absurdIndex v
lookup (Snoc _ val) Zero = val
lookup (Snoc env _) (Succ v) = lookup env v
lookup _ _ = panic "lookupValue"

type Size v = Index (Succ v)

extendSize :: Size v -> (Size (Succ v), Level)
extendSize f = (Succ f, Index.toLevel Zero $ Succ f)
