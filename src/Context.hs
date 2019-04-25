module Context where

import Protolude

import qualified Bound.Var as Bound

import qualified Domain
import qualified Syntax

data Binding = Binding
  { name :: !Text
  , value :: Domain.Value
  , type_ :: Domain.Type
  }

data Context v = Context
  { environment :: Syntax.Env Binding v
  , values :: Domain.Env v
  }

extend
  :: Context v
  -> Text
  -> Domain.Type
  -> Context (Bound.Var () v)
extend (Context env vals) n t =
  let
    (vals', v) =
      Domain.extend vals
  in
  Context
    (Syntax.Snoc env (Binding n (Domain.var v) t))
    vals'

extendValue
  :: Context v
  -> Text
  -> Domain.Type
  -> Domain.Value
  -> Context (Bound.Var () v)
extendValue (Context env vals) n v t =
  let
    (vals', _) =
      Domain.extend vals
  in
  Context
    (Syntax.Snoc env (Binding n v t))
    vals'

lookupName :: Text -> Context v -> Maybe (v, Binding)
lookupName name (Context env _) = Syntax.lookupIndex env $ \(Binding name' _ _) -> name == name'
