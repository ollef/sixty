module Syntax where

import Protolude

import Index
import qualified Meta

data Term v
  = Var !(Index v)
  | Global !Text
  | Meta !Meta.Index
  | Let !(Term v) !(Scope Term v)
  | Pi !(Term v) !(Scope Term v)
  | Fun !(Term v) !(Term v)
  | Lam !(Scope Term v)
  | App !(Term v) !(Term v)
  deriving Show

type Type = Term

apps :: Foldable f => Term v -> f (Term v) -> Term v
apps = foldl App
