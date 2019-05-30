{-# language OverloadedStrings #-}
module Builtin where

import Protolude

import qualified Domain
import qualified Name

typeName :: IsString s => s
typeName = "Builtin.Type"

type_ :: Domain.Value
type_ = Domain.global typeName

fail :: Name.Qualified
fail = "Builtin.fail"
