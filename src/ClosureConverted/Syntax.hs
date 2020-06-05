{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module ClosureConverted.Syntax where

import Protolude hiding (Type, IntMap)

import Data.Persist
import Unsafe.Coerce

import Data.OrderedHashMap (OrderedHashMap)
import Index
import Literal (Literal)
import Name (Name)
import qualified Name
import Syntax.Telescope (Telescope)

{-
General idea:

xs |- t : T
-------------------------
|- \xs. t : Function xs T

f : Function xs T
ts : xs[ts/xs]
-----------------
f ts : T[ts/xs]

f : Function (xs ++ ys) T
ts : xs[ts/xs]
--------------------------------------
Closure f ts : ys[ts/xs] -> T[ts/xs]

cl : (xs ++ ys) -> T
ts : xs[ts/xs]
------------------------------------------
ApplyClosure cl ts : ys[ts/xs] -> T[ts/xs]
-}

data Term v
  = Var !(Index v)
  | Global !Name.Lifted
  | Con -- ^ Saturated constructor application
    !Name.QualifiedConstructor
    [Term v] -- ^ Type parameters
    [Term v] -- ^ Constructor arguments
  | Lit !Literal
  | Let !Name !(Term v) !(Type v) !(Scope Term v)
  | Function !(Telescope Type Type Void) -- ^ The type of a top-level function definition
  | Apply !Name.Lifted [Term v] -- ^ Saturated application of a top-level function
  | Pi !Name !(Type v) !(Scope Type v)
  | Closure !Name.Lifted [Term v]
  | ApplyClosure !(Term v) [Term v]
  | Case !(Term v) (Branches v) !(Maybe (Term v))
  deriving (Eq, Show, Generic, Persist, Hashable)

type Type = Term

data Branches v
  = ConstructorBranches !Name.Qualified (ConstructorBranches v)
  | LiteralBranches (LiteralBranches v)
  deriving (Eq, Show, Generic, Persist, Hashable)

type ConstructorBranches v =
  OrderedHashMap Name.Constructor (Telescope Type Term v)

type LiteralBranches v =
  OrderedHashMap Literal (Term v)

data Definition
  = TypeDeclaration !(Type Void)
  | ConstantDefinition !(Term Void)
  | FunctionDefinition !(Telescope Type Term Void)
  | DataDefinition (ConstructorDefinitions Void)
  | ParameterisedDataDefinition !(Telescope Type ConstructorDefinitions Void)
  deriving (Eq, Show, Generic, Persist, Hashable)

newtype ConstructorDefinitions v =
  ConstructorDefinitions (OrderedHashMap Name.Constructor (Type v))
  deriving (Eq, Show, Generic, Persist, Hashable)

fromVoid :: Term Void -> Term v
fromVoid =
  unsafeCoerce
