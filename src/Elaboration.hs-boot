module Elaboration where

import Protolude

import Data.HashSet (HashSet)
import Data.Text.Prettyprint.Doc (Doc)

import Context (Context)
import qualified Core.Domain as Domain
import Literal (Literal)
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified Presyntax
import qualified Core.Syntax as Syntax

check
  :: Context v
  -> Presyntax.Term
  -> Domain.Type
  -> M (Syntax.Term v)

inferLiteral :: Literal -> Domain.Type

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

data ResolvedConstructor
  = Ambiguous (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | ResolvedConstructor !Name.QualifiedConstructor
  | ResolvedData !Name.Qualified

resolveConstructor
  :: HashSet Name.QualifiedConstructor
  -> HashSet Name.Qualified
  -> M (Maybe Name.Qualified)
  -> M ResolvedConstructor

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
