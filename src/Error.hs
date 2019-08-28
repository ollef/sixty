{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Error where

import Protolude

import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)

import qualified Meta
import Name (Name)
import qualified Name
import Plicity
import qualified Position
import qualified Scope
import qualified Span

data Error
  = Parse FilePath !Parsing
  | DuplicateName !Scope.KeyedName
  | Elaboration !Scope.KeyedName !Error.Spanned
  deriving (Eq, Ord, Show, Generic, Hashable)

data Elaboration
  = NotInScope !Name.Pre
  | Ambiguous !Name.Pre (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | TypeMismatch
  | OccursCheck
  | UnsolvedMetaVariable !Meta.Index
  | NonExhaustivePatterns
  | OverlappingPatterns
  | PlicityMismatch !PlicityMismatch -- TODO needs field/argument distinction for printing
  | UnableToInferImplicitLambda
  | ImplicitApplicationMismatch (HashMap Name ())
  deriving (Eq, Ord, Show, Generic, Hashable)

data PlicityMismatch
  = Mismatch !Plicity !Plicity
  | Missing !Plicity
  | Extra
  deriving (Eq, Ord, Show, Generic, Hashable)

data Spanned
  = Spanned !Span.Relative !Error.Elaboration
  deriving (Eq, Ord, Show, Generic, Hashable)

data Parsing = Parsing
  { reason :: !(Maybe Text)
  , expected :: [Text]
  , position :: !Position.Absolute
  } deriving (Eq, Ord, Show, Generic, Hashable)
