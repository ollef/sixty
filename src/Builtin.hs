{-# language OverloadedStrings #-}
module Builtin where

import qualified Domain
import qualified Name

module_ :: Name.Module
module_ =
  "Sixten.Builtin"

typeName :: Name.Qualified
typeName =
  "Sixten.Builtin.Type"

type_ :: Domain.Value
type_ =
  Domain.global typeName

fail :: Name.Qualified
fail =
  "Sixten.Builtin.fail"
