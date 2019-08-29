{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language StandaloneDeriving #-}
module Error where

import Protolude

import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)

import qualified Error.Parsing as Error
import qualified Meta
import Data.Tsil (Tsil)
import Name (Name)
import qualified Name
import Plicity
import qualified Scope
import qualified Span
import qualified Syntax

data Error
  = Parse FilePath !Error.Parsing
  | DuplicateName !Scope.KeyedName
  | Elaboration !Scope.KeyedName !Error.Spanned
  deriving (Eq, Show, Generic, Hashable)

data Elaboration
  = NotInScope !Name.Pre
  | Ambiguous !Name.Pre (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | TypeMismatch (Tsil (PrettyableTerm, PrettyableTerm))
  | OccursCheck
  | UnsolvedMetaVariable !Meta.Index
  | NonExhaustivePatterns
  | OverlappingPatterns
  | PlicityMismatch !PlicityMismatch -- TODO needs field/argument distinction for printing
  | UnableToInferImplicitLambda
  | ImplicitApplicationMismatch (HashMap Name ())
  deriving (Eq, Show, Generic, Hashable)

data PlicityMismatch
  = Mismatch !Plicity !Plicity
  | Missing !Plicity
  | Extra
  deriving (Eq, Show, Generic, Hashable)

data Spanned
  = Spanned !Span.Relative !Error.Elaboration
  deriving (Eq, Show, Generic, Hashable)

data V

data PrettyableTerm = PrettyableTerm Name.Module [Name] (Syntax.Term V)
  deriving (Eq, Show, Generic, Hashable)
