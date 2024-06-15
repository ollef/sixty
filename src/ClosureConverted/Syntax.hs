{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module ClosureConverted.Syntax where

import Boxity
import Data.OrderedHashMap (OrderedHashMap)
import Index (Index, Scope)
import qualified Index
import Literal (Literal)
import Name (Name)
import qualified Name
import Protolude hiding (IntMap, Type)
import Telescope (Telescope)
import Unsafe.Coerce

{-
General idea:

xs |- t : T
-------------------------
\|- \xs. t : Function xs T

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
  | -- | Saturated constructor application
    Con
      !Name.QualifiedConstructor
      [Term v]
      -- ^ Type parameters
      [Term v]
      -- ^ Constructor arguments
  | Lit !Literal
  | Let !Name !(Term v) !(Type v) !(Scope Term v)
  | -- | The type of a top-level function definition
    Function !(Telescope Name Type Type Index.Zero)
  | -- | Saturated application of a top-level function
    Apply !Name.Lifted [Term v]
  | Pi !Name !(Type v) !(Scope Type v)
  | Closure !Name.Lifted [Term v]
  | ApplyClosure !(Term v) [Term v]
  | Case !(Term v) !(Type v) (Branches v) !(Maybe (Term v))
  deriving (Eq, Show, Generic, Hashable)

type Type = Term

data Branches v
  = ConstructorBranches !Name.Qualified (ConstructorBranches v)
  | LiteralBranches (LiteralBranches v)
  deriving (Eq, Show, Generic, Hashable)

type ConstructorBranches v =
  OrderedHashMap Name.Constructor (Telescope Name Type Term v)

type LiteralBranches v =
  OrderedHashMap Literal (Term v)

data Definition
  = TypeDeclaration !(Type Index.Zero)
  | ConstantDefinition !(Term Index.Zero)
  | FunctionDefinition !(Telescope Name Type Term Index.Zero)
  | DataDefinition !Boxity (ConstructorDefinitions Index.Zero)
  | ParameterisedDataDefinition !Boxity !(Telescope Name Type ConstructorDefinitions Index.Zero)
  deriving (Eq, Show, Generic, Hashable)

newtype ConstructorDefinitions v
  = ConstructorDefinitions (OrderedHashMap Name.Constructor (Type v))
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)

fromZero :: Term Index.Zero -> Term v
fromZero =
  unsafeCoerce
