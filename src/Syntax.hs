module Syntax where

import Protolude hiding (Type)

import Index
import qualified Meta

data Term v
  = Var !(Index v)
  | Global !Text
  | Meta !Meta.Index
  | Let !Text !(Term v) !(Type v) !(Scope Term v)
  | Pi !Text !(Type v) !(Scope Type v)
  | Fun !(Type v) !(Type v)
  | Lam !Text !(Type v) !(Scope Term v)
  | App !(Term v) !(Term v)
  deriving Show

type Type = Term

apps :: Foldable f => Term v -> f (Term v) -> Term v
apps = foldl App
