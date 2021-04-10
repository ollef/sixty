{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Builtin where

import qualified Core.Domain as Domain
import qualified Core.Syntax as Syntax
import qualified Data.Tsil as Tsil
import qualified Name
import Plicity

pattern Module :: Name.Module
pattern Module =
  "Sixten.Builtin"

pattern TypeName :: Name.Qualified
pattern TypeName =
  "Sixten.Builtin.Type"

pattern Type :: Domain.Value
pattern Type =
  Domain.Neutral (Domain.Global TypeName) Domain.Empty

type_ :: Syntax.Term v
type_ =
  Syntax.Global TypeName

pattern FailName :: Name.Qualified
pattern FailName =
  "Sixten.Builtin.fail"

pattern Fail :: Domain.Type -> Domain.Value
pattern Fail type_ =
  Domain.Neutral (Domain.Global FailName) (Domain.Apps (Tsil.Empty Tsil.:> (Explicit, type_)))

pattern UnitName :: Name.Qualified
pattern UnitName =
  "Sixten.Builtin.Unit"

fail :: Syntax.Type v -> Syntax.Term v
fail =
  Syntax.App (Syntax.Global Builtin.FailName) Explicit

pattern EqualsName :: Name.Qualified
pattern EqualsName =
  "Sixten.Builtin.Equals"

pattern Equals ::
  Domain.Type ->
  Domain.Value ->
  Domain.Value ->
  Domain.Value
pattern Equals k a b =
  Domain.Neutral
    (Domain.Global EqualsName)
    (Domain.Apps (Tsil.Empty Tsil.:> (Implicit, k) Tsil.:> (Explicit, a) Tsil.:> (Explicit, b)))

equals ::
  Syntax.Type v ->
  Syntax.Term v ->
  Syntax.Term v ->
  Syntax.Term v
equals k a b =
  Syntax.apps
    (Syntax.Global EqualsName)
    [(Implicit, k), (Explicit, a), (Explicit, b)]

pattern ReflName :: Name.QualifiedConstructor
pattern ReflName =
  Name.QualifiedConstructor EqualsName "Refl"

pattern Refl ::
  Domain.Type ->
  Domain.Value ->
  Domain.Value ->
  Domain.Value
pattern Refl k a b =
  Domain.Con
    ReflName
    (Tsil.Empty Tsil.:> (Implicit, k) Tsil.:> (Implicit, a) Tsil.:> (Implicit, b))

pattern IntName :: Name.Qualified
pattern IntName =
  "Sixten.Builtin.Int"

pattern Int :: Domain.Value
pattern Int =
  Domain.Neutral (Domain.Global IntName) Domain.Empty

int :: Syntax.Term v
int =
  Syntax.Global IntName

pattern EmptyRepresentationName :: Name.Qualified
pattern EmptyRepresentationName =
  "Sixten.Builtin.EmptyRepresentation"

pattern WordRepresentationName :: Name.Qualified
pattern WordRepresentationName =
  "Sixten.Builtin.WordRepresentation"

pattern AddRepresentationName :: Name.Qualified
pattern AddRepresentationName =
  "Sixten.Builtin.addRepresentation"

pattern MaxRepresentationName :: Name.Qualified
pattern MaxRepresentationName =
  "Sixten.Builtin.maxRepresentation"
