{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Syntax.ClosureConverted where

import Protolude hiding (Type, IntMap)

import Data.HashMap.Lazy (HashMap)

import Binding (Binding)
import Index
import qualified Name
import Plicity
import Syntax.Telescope (Telescope)

data Term v
  = Var !(Index v)
  | Global !Name.Lifted
  | ApplyGlobal !Name.Lifted [Term v]
  | ApplyUnknown !(Term v) [(Plicity, Term v)]
  | Con !Name.QualifiedConstructor [(Plicity, Term v)]
  | Let !Binding !(Term v) !(Type v) !(Scope Term v)
  | Pi !Binding !(Type v) !Plicity !(Scope Type v)
  | Fun !(Type v) !Plicity !(Type v)
  | Case !(Term v) (Branches v) !(Maybe (Term v))
  deriving (Eq, Show, Generic, Hashable)

type Type = Term

type Branches v = HashMap Name.QualifiedConstructor (Telescope Type Term v)

data Definition
  = ConstantDefinition !(Telescope Type Term Void)
  | DataDefinition (Telescope Type ConstructorDefinitions Void)
  deriving (Show, Generic, Hashable)

newtype ConstructorDefinitions v =
  ConstructorDefinitions (HashMap Name.Constructor (Type v))
  deriving (Show, Generic, Hashable)
