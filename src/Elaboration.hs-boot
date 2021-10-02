module Elaboration where

import Protolude

import Data.HashSet (HashSet)
import Prettyprinter (Doc)

import qualified Core.Domain as Domain
import qualified Core.Syntax as Syntax
import Elaboration.Context (Context)
import Literal (Literal)
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified Postponement
import qualified Surface.Syntax as Surface

check
  :: Context v
  -> Surface.Term
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
  -> M (Maybe (Either Meta.Index Name.Qualified))

data ResolvedConstructor
  = Ambiguous (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | ResolvedConstructor !Name.QualifiedConstructor
  | ResolvedData !Name.Qualified

resolveConstructor
  :: HashSet Name.QualifiedConstructor
  -> HashSet Name.Qualified
  -> M (Maybe (Either Meta.Index Name.Qualified))
  -> M (Either Meta.Index ResolvedConstructor)

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

postpone
  :: Context v
  -> Domain.Type
  -> Meta.Index
  -> (Postponement.CanPostpone -> M (Syntax.Term v))
  -> M (Syntax.Term v)
