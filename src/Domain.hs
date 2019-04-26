{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
module Domain where

import Protolude hiding (Type)

import Bound.Scope.Simple
import qualified Bound.Var as Bound
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import Monad
import qualified Syntax
import Tsil (Tsil)
import qualified Tsil

data Closure where
  Closure :: Syntax.Env (Lazy Value) v -> Scope () Syntax.Term v -> Closure

data Value
  = Neutral Head Spine
  | Lam !Closure
  | Pi !(Lazy Type) !Closure
  | Fun !(Lazy Type) !(Lazy Type)

type Type = Value

data Head
  = Var !Var
  | Global !Text

type Spine = Tsil (Lazy Value)

newtype Var = V Int
  deriving (Eq, Ord, Show, Hashable, Num)

data Env val = Env
  { fresh :: !Int
  , vars :: HashMap Var val
  }

var :: Var -> Value
var v = Neutral (Var v) Tsil.Nil

global :: Text -> Value
global g = Neutral (Global g) Tsil.Nil

lookupEnv :: Env val -> Var -> val
lookupEnv (Env _ vs) v =
  vs HashMap.! v

extend :: Env val -> (Env (Bound.Var () val), Var)
extend (Env f vs) =
  (Env (f + 1) (HashMap.insert v (Bound.B ()) $ Bound.F <$> vs), v)
  where
    v = V f

newtype EnvSize v = EnvSize Int

extendEnvSize :: EnvSize v -> (EnvSize (Bound.Var () val), Var)
extendEnvSize (EnvSize f) = (EnvSize $ f + 1, V f)
