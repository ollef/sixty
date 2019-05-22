{-# language OverloadedStrings #-}
module Builtin where

import qualified Domain
import qualified Name

typeName :: Name.Qualified
typeName = "Builtin.Type"

type_ :: Domain.Value
type_ = Domain.global typeName

fail :: Name.Qualified
fail = "Builtin.fail"
