module Context where

import Protolude

import qualified Bound.Var as Bound

import qualified Domain
import Index
import Monad
import qualified Syntax

data Context v = Context
  { size :: !(Domain.EnvSize v)
  , names :: Syntax.Env Text v
  , values :: Syntax.Env (Lazy Domain.Value) v
  , types :: Syntax.Env (Lazy Domain.Type) v
  }

extend
  :: Context v
  -> Text
  -> Lazy Domain.Type
  -> (Context (Bound.Var () v), Domain.Var)
extend (Context sz ns vs ts) n t =
  let
    (sz', v) =
      Domain.extendEnvSize sz
  in
  ( Context
    sz'
    (Syntax.Snoc ns n)
    (Syntax.Snoc vs $ Lazy $ pure $ Domain.var v)
    (Syntax.Snoc ts t)
  , v
  )

extendValue
  :: Context v
  -> Text
  -> Lazy Domain.Type
  -> Lazy Domain.Value
  -> Context (Bound.Var () v)
extendValue (Context sz ns vs ts) n v t =
  let
    (sz', _) =
      Domain.extendEnvSize sz
  in
  Context
    sz'
    (Syntax.Snoc ns n)
    (Syntax.Snoc vs v)
    (Syntax.Snoc ts t)

lookupName :: Text -> Context v -> Maybe (Index v)
lookupName name context = fst <$> Syntax.lookupIndex (names context) (== name)

lookupValue :: Index v -> Context v -> Lazy Domain.Value
lookupValue v context = Syntax.lookupValue (values context) v

lookupType :: Index v -> Context v -> Lazy Domain.Type
lookupType v context = Syntax.lookupValue (types context) v
