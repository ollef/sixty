module Elaboration where

import Protolude

import Data.HashSet (HashSet)
import Data.Text.Prettyprint.Doc (Doc)

import Context (Context)
import qualified Domain
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified Presyntax
import qualified Syntax

check
  :: Context v
  -> Presyntax.Term
  -> Domain.Type
  -> M (Syntax.Term v)

evaluate
  :: Context v
  -> Syntax.Term v
  -> M Domain.Value

readback
  :: Context v
  -> Domain.Value
  -> M (Syntax.Term v)

getExpectedTypeName
  :: Context v
  -> Domain.Type
  -> M (Maybe Name.Qualified)

resolveConstructor
  :: Context v
  -> Name.Pre
  -> HashSet Name.QualifiedConstructor
  -> M (Maybe Name.Qualified)
  -> M (Maybe Name.QualifiedConstructor)

inferenceFailed
  :: Context v
  -> M (Syntax.Term v, Domain.Type)

data InsertUntil
  = UntilTheEnd
  | UntilExplicit
  | UntilImplicit (Name -> Bool)

insertMetas
  :: Context v
  -> InsertUntil
  -> Domain.Type
  -> M ([(Plicity, Domain.Value)], Domain.Type)

prettyValue :: Context v -> Domain.Value -> M (Doc ann)
