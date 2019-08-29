{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Error where

import Protolude

import Data.HashSet (HashSet)
import Data.Text.Prettyprint.Doc

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
  | PlicityMismatch !FieldOrArgument !PlicityMismatch
  | UnableToInferImplicitLambda
  | ImplicitApplicationMismatch (HashSet Name) !PrettyableTerm !PrettyableTerm
  deriving (Eq, Show, Generic, Hashable)

data PlicityMismatch
  = Mismatch !Plicity !Plicity
  | Missing !Plicity
  | Extra
  deriving (Eq, Show, Generic, Hashable)

data FieldOrArgument
  = Field
  | Argument
  deriving (Eq, Show, Generic, Hashable)

instance Pretty FieldOrArgument where
  pretty fieldOrArg =
    case fieldOrArg of
      Field ->
        "field"

      Argument ->
        "argument"

data Spanned
  = Spanned !Span.Relative !Error.Elaboration
  deriving (Eq, Show, Generic, Hashable)

data V

data PrettyableTerm = PrettyableTerm Name.Module [Name] (Syntax.Term V)
  deriving (Eq, Show, Generic, Hashable)
