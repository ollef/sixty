{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
module Builtin where

import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Name
import Plicity

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

pattern EqualsName :: Name.Qualified
pattern EqualsName =
  "Sixten.Builtin.Equals"

pattern Equals
  :: Domain.Type
  -> Domain.Value
  -> Domain.Value
  -> Domain.Value
pattern Equals k a b =
  Domain.Neutral
    (Domain.Global EqualsName)
    (Tsil.Empty Tsil.:> (Implicit, k) Tsil.:> (Explicit, a) Tsil.:> (Explicit, b))

pattern ReflName :: Name.QualifiedConstructor
pattern ReflName =
  Name.QualifiedConstructor EqualsName "Refl"

pattern Refl
  :: Domain.Type
  -> Domain.Value
  -> Domain.Value
  -> Domain.Value
pattern Refl k a b =
  Domain.Neutral
    (Domain.Con ReflName)
    (Tsil.Empty Tsil.:> (Implicit, k) Tsil.:> (Explicit, a) Tsil.:> (Explicit, b))
