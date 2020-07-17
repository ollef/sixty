{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Applicative.Syntax where

import Protolude hiding (Type, IntMap)

import Data.Persist
import Unsafe.Coerce

import Data.OrderedHashMap (OrderedHashMap)
import Index
import Literal (Literal)
import Name (Name)
import qualified Name
import Telescope (Telescope)

data Term v
  = Operand !(Operand v)
  | Con -- ^ Saturated constructor application
    !Name.QualifiedConstructor
    [Operand v] -- ^ Type parameters
    [Operand v] -- ^ Constructor arguments
  | Let !Name !(Term v) !(TypeOperand v) !(Scope Term v)
  | Function !(Telescope Name Type Type Void) -- ^ The type of a top-level function definition
  | Apply !Name.Lifted [Operand v] -- ^ Saturated application of a top-level function
  | Pi !Name !(Type v) !(Scope Type v)
  | Closure !Name.Lifted [Operand v]
  | ApplyClosure !(Operand v) [Operand v]
  | Case !(Operand v) (Branches v) !(Maybe (Term v))
  deriving (Eq, Show, Generic, Persist, Hashable)

type Type = Term

data Operand v
  = Var !(Index v)
  | Global !Name.Lifted
  | Lit !Literal
  deriving (Eq, Show, Generic, Persist, Hashable)

type TypeOperand = Operand

data Branches v
  = ConstructorBranches !Name.Qualified (ConstructorBranches v)
  | LiteralBranches (LiteralBranches v)
  deriving (Eq, Show, Generic, Persist, Hashable)

type ConstructorBranches v =
  OrderedHashMap Name.Constructor (Telescope Name Type Term v)

type LiteralBranches v =
  OrderedHashMap Literal (Term v)

data Definition
  = TypeDeclaration !(Type Void)
  | ConstantDefinition !(Term Void)
  | FunctionDefinition !(Telescope Name Type Term Void)
  | DataDefinition (ConstructorDefinitions Void)
  | ParameterisedDataDefinition !(Telescope Name Type ConstructorDefinitions Void)
  deriving (Eq, Show, Generic, Persist, Hashable)

newtype ConstructorDefinitions v =
  ConstructorDefinitions (OrderedHashMap Name.Constructor (Type v))
  deriving (Eq, Show, Generic, Persist, Hashable)

fromVoid :: Term Void -> Term v
fromVoid =
  unsafeCoerce
