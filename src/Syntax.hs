module Syntax where

import Protolude

import Bound.Var
import Bound.Scope.Simple
import Index

data Term v
  = Var !(Index v)
  | Global !Text
  | Let !(Term v) !(Scope () Term v)
  | Pi !(Term v) !(Scope () Term v)
  | Fun !(Term v) !(Term v)
  | Lam !(Scope () Term v)
  | App !(Term v) !(Term v)

type Type = Term
