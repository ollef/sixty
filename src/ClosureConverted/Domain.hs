{-# language GADTs #-}
module ClosureConverted.Domain where

import Protolude hiding (Type, evaluate)

import qualified ClosureConverted.Syntax as Syntax
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Index
import Literal (Literal)
import Monad
import Name (Name)
import qualified Name
import Telescope (Telescope)
import Var (Var)

data Value
  = Neutral !Head Spine
  | Con !Name.QualifiedConstructor [Value] [Value]
  | Lit !Literal
  | Glued !Head Spine !Value
  | Lazy !(Lazy Value)
  | Pi !Name !Type !Closure
  | Function !(Telescope Name Syntax.Type Syntax.Type Void)

data Head
  = Var !Var
  | Global !Name.Lifted

type Type = Value

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

-------------------------------------------------------------------------------
-- * Elimination spines

type Spine = Tsil Elimination

data Elimination
  = App !Value
  | Case !Branches

data GroupedElimination
  = GroupedApps [Value]
  | GroupedCase !Branches

groupSpine :: Spine -> [GroupedElimination]
groupSpine =
  go Tsil.Empty . toList
  where
    go args (App arg : spine) =
      go (args Tsil.:> arg) spine
    go Tsil.Empty (Case branches : spine) =
      GroupedCase branches : go Tsil.Empty spine
    go args (Case branches : spine) =
      GroupedApps (toList args) : GroupedCase branches : go Tsil.Empty spine
    go Tsil.Empty [] =
      []
    go args [] =
      [GroupedApps $ toList args]
