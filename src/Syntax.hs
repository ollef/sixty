module Syntax where

import Protolude

import Index

data Term v
  = Var !(Index v)
  | Global !Text
  | Let !(Term v) !(Scope Term v)
  | Pi !(Term v) !(Scope Term v)
  | Fun !(Term v) !(Term v)
  | Lam !(Scope Term v)
  | App !(Term v) !(Term v)
  deriving Show

type Type = Term
