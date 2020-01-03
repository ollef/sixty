{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module LambdaLifted.Syntax where

import Protolude hiding (Type, IntMap)

import Data.HashMap.Lazy (HashMap)

import Index
import Literal (Literal)
import Name (Name)
import qualified Name
import Syntax.Telescope (Telescope)

data Term v
  = Var !(Index v)
  | Global !Name.Lifted
  | Con !Name.QualifiedConstructor [Term v]
  | Lit !Literal
  | Let !Name !(Term v) !(Type v) !(Scope Term v)
  | Pi !Name !(Type v) !(Scope Type v)
  | App !(Term v) !(Term v)
  | Case !(Term v) (Branches v) !(Maybe (Term v))
  deriving (Eq, Show, Generic, Hashable)

type Type = Term

data Branches v
  = ConstructorBranches (HashMap Name.QualifiedConstructor (Telescope Type Term v))
  | LiteralBranches (HashMap Literal (Term v))
  deriving (Eq, Show, Generic, Hashable)

data Definition
  = ConstantDefinition !(Telescope Type Term Void)
  | DataDefinition !(Telescope Type ConstructorDefinitions Void)
  deriving (Show, Generic, Hashable)

newtype ConstructorDefinitions v =
  ConstructorDefinitions (HashMap Name.Constructor (Type v))
  deriving (Show, Generic, Hashable)
