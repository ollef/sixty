{-# LANGUAGE KindSignatures #-}

module Elaboration.Context.Type where

import qualified Core.Domain as Domain
import Data.EnumMap (EnumMap)
import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import Data.IORef.Lifted
import Data.IntSeq (IntSeq)
import qualified Data.Kind
import Data.Tsil (Tsil)
import qualified Elaboration.Meta as Meta
import qualified Elaboration.Postponed as Postponed
import Error (Error)
import qualified Error
import qualified Index.Map as Index
import Literal (Literal)
import Monad
import Name (Name)
import qualified Name
import Protolude hiding (catch, check, force, moduleName, state)
import qualified Scope
import qualified Span
import Var

data Context (v :: Data.Kind.Type) = Context
  { definitionKind :: !Scope.DefinitionKind
  , definitionName :: !Name.Qualified
  , definitionType :: Maybe Domain.Type
  , span :: !Span.Relative
  , indices :: Index.Map v Var
  , surfaceNames :: HashMap Name.Surface (Domain.Value, Domain.Type)
  , varNames :: EnumMap Var Name
  , types :: EnumMap Var Domain.Type
  , boundVars :: IntSeq Var
  , metas :: !(IORef (Meta.State M))
  , postponed :: !(IORef Postponed.Checks)
  , values :: EnumMap Var Domain.Value
  , equal :: HashMap Domain.Head [(Domain.Spine, Domain.Value)]
  , notEqual :: HashMap Domain.Head [(Domain.Spine, HashSet Name.QualifiedConstructor, HashSet Literal)]
  , coverageChecks :: !(IORef (Tsil CoverageCheck))
  , errors :: !(IORef (Tsil Error))
  }

type CoveredConstructors = EnumMap Var (HashSet Name.QualifiedConstructor)

type CoveredLiterals = EnumMap Var (HashSet Literal)

data CoverageCheck = CoverageCheck
  { allClauses :: Set Span.Relative
  , usedClauses :: IORef (Set Span.Relative)
  , matchKind :: !Error.MatchKind
  }
