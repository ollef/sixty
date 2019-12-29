{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module LambdaLifted.Syntax where

import Protolude hiding (Type, IntMap)

import Data.HashMap.Lazy (HashMap)

import Binding (Binding)
import Index
import Literal (Literal)
import qualified Name
import Plicity
import Syntax.Telescope (Telescope)

data Term v
  = Var !(Index v)
  | Global !Name.Lifted
  | Con !Name.QualifiedConstructor [(Plicity, Term v)]
  | Lit !Literal
  | Let !Binding !(Term v) !(Type v) !(Scope Term v)
  | Pi !Binding !(Type v) !Plicity !(Scope Type v)
  | Fun !(Type v) !Plicity !(Type v)
  | App !(Term v) !Plicity !(Term v)
  | Case !(Term v) (Branches v) !(Maybe (Term v))
  deriving (Eq, Show, Generic, Hashable)

type Type = Term

data Branches v
  = ConstructorBranches (HashMap Name.QualifiedConstructor (Telescope Type Term v))
  | LiteralBranches (HashMap Literal (Term v))
  deriving (Eq, Show, Generic, Hashable)

data Definition
  = ConstantDefinition !(Telescope Type Term Void)
  | DataDefinition (Telescope Type ConstructorDefinitions Void)
  deriving (Show, Generic, Hashable)

newtype ConstructorDefinitions v =
  ConstructorDefinitions (HashMap Name.Constructor (Type v))
  deriving (Show, Generic, Hashable)
