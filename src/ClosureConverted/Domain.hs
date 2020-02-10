{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
module ClosureConverted.Domain where

import Protolude hiding (Type, evaluate)

import Name (Name)
import qualified ClosureConverted.Syntax as Syntax
import qualified Environment
import Literal (Literal)
import qualified Name
import Syntax.Telescope (Telescope)
import Index
import Var (Var)

data Value
  = Neutral !Head Spine
  | Con !Name.QualifiedConstructor [Value] [Value]
  | Lit !Literal
  | Pi !Name !Type !Closure
  | Function !(Telescope Syntax.Type Syntax.Type Void)

data Head
  = Var !Var
  | Global !Name.Lifted
  | Case !Value !Branches

type Type = Value

type Spine = [Value]

data Branches where
  Branches :: Environment v -> Syntax.Branches v -> Maybe (Syntax.Term v) -> Branches

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

type Environment = Environment.Environment Value

var :: Var -> Value
var v =
  Neutral (Var v) mempty

global :: Name.Lifted -> Value
global g =
  Neutral (Global g) mempty
