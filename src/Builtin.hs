{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
module Builtin where

import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Name
import Plicity
import qualified Syntax

pattern Module :: Name.Module
pattern Module =
  "Sixten.Builtin"

pattern TypeName :: Name.Qualified
pattern TypeName =
  "Sixten.Builtin.Type"

pattern Type :: Domain.Value
pattern Type =
  Domain.Neutral (Domain.Global TypeName) Tsil.Empty

type_ :: Syntax.Term v
type_ =
  Syntax.Global TypeName

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

equals
  :: Syntax.Type v
  -> Syntax.Term v
  -> Syntax.Term v
  -> Syntax.Term v
equals k a b =
  Syntax.apps (Syntax.Global EqualsName)
    [(Implicit, k), (Explicit, a), (Explicit, b)]

pattern ReflName :: Name.QualifiedConstructor
pattern ReflName =
  Name.QualifiedConstructor EqualsName "Refl"

pattern Refl
  :: Domain.Type
  -> Domain.Value
  -> Domain.Value
  -> Domain.Value
pattern Refl k a b =
  Domain.Con
    ReflName
    (Tsil.Empty Tsil.:> (Implicit, k) Tsil.:> (Explicit, a) Tsil.:> (Explicit, b))

pattern IntName :: Name.Qualified
pattern IntName =
  "Sixten.Builtin.Int"

pattern Int :: Domain.Value
pattern Int =
  Domain.Neutral (Domain.Global IntName) Tsil.Empty

int :: Syntax.Term v
int =
  Syntax.Global IntName
