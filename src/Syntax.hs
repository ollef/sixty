{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language PackageImports #-}
{-# language RoleAnnotations #-}
module Syntax where

import Protolude hiding (Type, IntMap)

import Data.Coerce

import "this" Data.IntMap (IntMap)
import Index
import qualified Meta
import Name (Name)
import qualified Name
import Telescope (Telescope)

data Term v
  = Var !(Index v)
  | Global !Name.Qualified
  | Meta !Meta.Index
  | Let !Name !(Term v) !(Type v) !(Scope Term v)
  | Pi !Name !(Type v) !(Scope Type v)
  | Fun !(Type v) !(Type v)
  | Lam !Name !(Type v) !(Scope Term v)
  | App !(Term v) !(Term v)
  deriving (Show, Generic, Hashable)

type Type = Term

apps :: Foldable f => Term v -> f (Term v) -> Term v
apps = foldl App

appsView :: Term v -> (Term v, [Term v])
appsView = go []
  where
    go args (App t1 t2) = go (t2 : args) t1
    go args t = (t, args)

succ :: Term v -> Term (Succ v)
succ = coerce

fromVoid :: Term Void -> Term v
fromVoid = coerce

type MetaSolutions =
  IntMap Meta.Index (Syntax.Term Void, Syntax.Type Void)

data Definition
  = TypeDeclaration !(Type Void)
  | ConstantDefinition !(Term Void)
  | DataDefinition (Telescope Type ConstructorDefinitions Void)
  deriving (Show, Generic, Hashable)

newtype ConstructorDefinitions v = ConstructorDefinitions [(Name.Constructor, Type v)]
  deriving (Show, Generic, Hashable)
