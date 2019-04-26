module Context where

import Protolude

import qualified Bound.Var as Bound

import qualified Domain
import qualified Syntax

data Context v = Context
  { size :: !(Domain.EnvSize v)
  , names :: Syntax.Env Text v
  , values :: Syntax.Env Domain.Value v
  , types :: Syntax.Env Domain.Type v
  }

extend
  :: Context v
  -> Text
  -> Domain.Type
  -> Context (Bound.Var () v)
extend (Context sz ns vs ts) n t =
  let
    (sz', v) =
      Domain.extendEnvSize sz
  in
  Context
    sz'
    (Syntax.Snoc ns n)
    (Syntax.Snoc vs $ Domain.var v)
    (Syntax.Snoc ts t)

extendValue
  :: Context v
  -> Text
  -> Domain.Type
  -> Domain.Value
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

lookupName :: Text -> Context v -> Maybe v
lookupName name context = fst <$> Syntax.lookupIndex (names context) (== name)

lookupValue :: v -> Context v -> Domain.Value
lookupValue v context = Syntax.lookupValue (values context) v

lookupType :: v -> Context v -> Domain.Type
lookupType v context = Syntax.lookupValue (types context) v
