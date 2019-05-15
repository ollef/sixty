{-# language RoleAnnotations #-}
module Syntax where

import Protolude hiding (Type)

import Data.Coerce

import Index
import qualified Meta
import Name (Name)
import qualified Name

data Term v
  = Var !(Index v)
  | Global !Name.Qualified
  | Meta !Meta.Index
  | Let !Name !(Term v) !(Type v) !(Scope Term v)
  | Pi !Name !(Type v) !(Scope Type v)
  | Fun !(Type v) !(Type v)
  | Lam !Name !(Type v) !(Scope Term v)
  | App !(Term v) !(Term v)
  deriving Show

type Type = Term

apps :: Foldable f => Term v -> f (Term v) -> Term v
apps = foldl App

succ :: Term v -> Term (Succ v)
succ = coerce
