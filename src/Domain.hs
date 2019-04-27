{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
module Domain where

import Protolude hiding (Type)

import Bound.Scope.Simple
import qualified Bound.Var as Bound

import Environment (Environment)
import qualified Environment
import Index
import Monad
import qualified Syntax
import Tsil (Tsil)
import qualified Tsil

data Closure where
  Closure :: Environment v (Lazy Value) -> Scope () Syntax.Term v -> Closure

data Value
  = Neutral Head Spine
  | Lam !Closure
  | Pi !(Lazy Type) !Closure
  | Fun !(Lazy Type) !(Lazy Type)

type Type = Value

data Head
  = Var !Level
  | Global !Text

type Spine = Tsil (Lazy Value)

var :: Level -> Value
var v = Neutral (Var v) Tsil.Nil

global :: Text -> Value
global g = Neutral (Global g) Tsil.Nil

type EnvSize v = Index (Bound.Var () v)

extendEnvSize :: EnvSize v -> (EnvSize (Bound.Var () v), Level)
extendEnvSize f = (Succ f, Index.toLevel Zero $ Succ f)
