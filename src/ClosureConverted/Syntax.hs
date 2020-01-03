{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module ClosureConverted.Syntax where

import Protolude hiding (Type, IntMap)

import Data.HashMap.Lazy (HashMap)

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
  | Con !Name.QualifiedConstructor [Term v]
  | Lit !Literal
  | Let !Name !(Term v) !(Type v) !(Scope Term v)
  | Function !(Telescope Type Type Void) -- ^ The type of a top-level function definition
  | Apply !Name.Lifted [Term v] -- ^ Saturated application of a top-level function
  | Pi !Name !(Type v) !(Scope Type v)
  | Closure !Name.Lifted [Term v]
  | ApplyClosure !(Term v) [Term v]
  | Case !(Term v) (Branches v) !(Maybe (Term v))
  deriving (Eq, Show, Generic, Hashable)

type Type = Term

data Branches v
  = ConstructorBranches (ConstructorBranches v)
  | LiteralBranches (LiteralBranches v)
  deriving (Eq, Show, Generic, Hashable)

type ConstructorBranches v =
  HashMap Name.QualifiedConstructor (Telescope Type Term v)

type LiteralBranches v =
  HashMap Literal (Term v)

data Definition
  = ConstantDefinition !(Term Void)
  | FunctionDefinition !(Telescope Type Term Void)
  | DataDefinition (ConstructorDefinitions Void)
  | ParameterisedDataDefinition !(Telescope Type ConstructorDefinitions Void)
  deriving (Show, Generic, Hashable)

newtype ConstructorDefinitions v =
  ConstructorDefinitions (HashMap Name.Constructor (Type v))
  deriving (Show, Generic, Hashable)
