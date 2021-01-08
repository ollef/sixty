{-# language DeriveGeneric #-}
{-# language DeriveAnyClass #-}
module LambdaLifted.Syntax where

import Protolude hiding (Type, IntMap)

import Data.Persist

import Boxity
import Data.OrderedHashMap (OrderedHashMap)
import Index
import Literal (Literal)
import Name (Name)
import qualified Name
import Telescope (Telescope)

data Term v
  = Var !(Index v)
  | Global !Name.Lifted
  | Con
    !Name.QualifiedConstructor
    [Term v] -- ^ Type parameters
    [Term v] -- ^ Constructor arguments
  | Lit !Literal
  | Let !Name !(Term v) !(Type v) !(Scope Term v)
  | Pi !Name !(Type v) !(Scope Type v)
  | App !(Term v) !(Term v)
  | Case !(Term v) (Branches v) !(Maybe (Term v))
  deriving (Eq, Show, Generic, Persist, Hashable)

type Type = Term

data Branches v
  = ConstructorBranches !Name.Qualified (OrderedHashMap Name.Constructor (Telescope Name Type Term v))
  | LiteralBranches (OrderedHashMap Literal (Term v))
  deriving (Eq, Show, Generic, Persist, Hashable)

data Definition
  = TypeDeclaration !(Type Void)
  | ConstantDefinition !(Telescope Name Type Term Void)
  | DataDefinition !Boxity !(Telescope Name Type ConstructorDefinitions Void)
  deriving (Eq, Show, Generic, Persist, Hashable)

newtype ConstructorDefinitions v =
  ConstructorDefinitions (OrderedHashMap Name.Constructor (Type v))
  deriving (Eq, Show, Generic, Persist, Hashable)
