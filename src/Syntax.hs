{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language PackageImports #-}
{-# language RoleAnnotations #-}
module Syntax where

import Protolude hiding (Type, IntMap)

import Data.HashMap.Lazy (HashMap)
import Unsafe.Coerce

import "this" Data.IntMap (IntMap)
import Index
import qualified Meta
import Name (Name)
import qualified Name
import Plicity
import qualified Span
import Syntax.Telescope (Telescope)

data Term v
  = Var !(Index v)
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Meta !Meta.Index
  | Let !Name !(Term v) !(Type v) !(Scope Term v)
  | Pi !Name !(Type v) !Plicity !(Scope Type v)
  | Fun !(Type v) !(Type v)
  | Lam !Name !(Type v) !Plicity !(Scope Term v)
  | App !(Term v) !Plicity !(Term v)
  | Case !(Term v) (Branches v) !(Maybe (Term v))
  | Spanned !Span.Relative !(Term v)
  deriving (Eq, Show, Generic, Hashable)

type Type = Term

type Branches v = HashMap Name.QualifiedConstructor (Telescope Type Term v)

implicitPi :: Name -> Type v -> Plicity -> Scope Type v -> Type v
implicitPi name type_ plicity =
  Pi name type_ (implicitise plicity)

apps :: Foldable f => Term v -> f (Plicity, Term v) -> Term v
apps = foldl (\fun (plicity, arg) -> App fun plicity arg)

appsView :: Term v -> (Term v, [Term v])
appsView = go []
  where
    go args (App t1 _ t2) = go (t2 : args) t1
    go args t = (t, args)

funs :: Foldable f => f (Term v) -> Term v -> Term v
funs args res = foldr Fun res args

succ :: Term v -> Term (Succ v)
succ = coerce

fromVoid :: Term Void -> Term v
fromVoid = coerce

coerce :: Term v -> Term v'
-- Can't be Data.Coerce.coerce anymore due to role limitations for Telescopes
coerce = unsafeCoerce

type MetaSolutions =
  IntMap Meta.Index (Syntax.Term Void, Syntax.Type Void)

data Definition
  = TypeDeclaration !(Type Void)
  | ConstantDefinition !(Term Void)
  | DataDefinition (Telescope Type ConstructorDefinitions Void)
  deriving (Show, Generic, Hashable)

newtype ConstructorDefinitions v =
  ConstructorDefinitions (HashMap Name.Constructor (Type v))
  deriving (Show, Generic, Hashable)
