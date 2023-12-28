{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module LambdaLifted.Syntax where

import Boxity
import Data.OrderedHashMap (OrderedHashMap)
import Index
import Literal (Literal)
import Name (Name)
import qualified Name
import Plicity
import Protolude hiding (IntMap, Type)
import Telescope (Telescope)
import qualified Telescope

data Term v
  = Var !(Index v)
  | Global !Name.Lifted
  | Con
      !Name.QualifiedConstructor
      [Term v]
      -- ^ Type parameters
      [Term v]
      -- ^ Constructor arguments
  | Lit !Literal
  | Let !Name !(Term v) !(Type v) !(Scope Term v)
  | Pi !Name !(Type v) !(Scope Type v)
  | App !(Term v) !(Term v)
  | Case !(Term v) (Branches v) !(Maybe (Term v))
  deriving (Eq, Show, Generic, Hashable)

type Type = Term

pisView :: (forall v'. Term v' -> term v') -> Term v -> Telescope Name term term v
pisView f type_ =
  case type_ of
    Var {} -> Telescope.Empty $ f type_
    Global {} -> Telescope.Empty $ f type_
    Con {} -> Telescope.Empty $ f type_
    Lit {} -> Telescope.Empty $ f type_
    Let {} -> Telescope.Empty $ f type_
    Pi name type' scope -> Telescope.Extend name (f type') Explicit $ pisView f scope
    App {} -> Telescope.Empty $ f type_
    Case {} -> Telescope.Empty $ f type_

data Branches v
  = ConstructorBranches !Name.Qualified (OrderedHashMap Name.Constructor (Telescope Name Type Term v))
  | LiteralBranches (OrderedHashMap Literal (Term v))
  deriving (Eq, Show, Generic, Hashable)

data Definition
  = TypeDeclaration !(Type Void)
  | ConstantDefinition !(Telescope Name Type Term Void)
  | DataDefinition !Boxity !(Telescope Name Type ConstructorDefinitions Void)
  deriving (Eq, Show, Generic, Hashable)

newtype ConstructorDefinitions v
  = ConstructorDefinitions (OrderedHashMap Name.Constructor (Type v))
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)
