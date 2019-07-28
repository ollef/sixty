module Elaboration where

import Protolude

import Data.HashSet (HashSet)

import Context (Context)
import qualified Domain
import Monad
import qualified Presyntax
import qualified Syntax
import qualified Name

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
  -> Lazy (Maybe Name.Qualified)
  -> M (Maybe Name.QualifiedConstructor)

inferenceFailed
  :: Context v
  -> M (Syntax.Term v, Domain.Type)
