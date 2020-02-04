{-# language OverloadedStrings #-}
module Error where

import Protolude

import Data.HashSet (HashSet)
import Data.Text.Prettyprint.Doc

import Data.Tsil (Tsil)
import Domain.Pattern (Pattern)
import qualified Error.Parsing as Error
import qualified Meta
import qualified Module
import Name (Name)
import qualified Name
import Plicity
import qualified Scope
import qualified Span
import qualified Syntax

data Error
  = Parse FilePath !Error.Parsing
  | DuplicateName !Scope.KeyedName
  | ImportNotFound !Name.Module !Module.Import
  | MultipleFilesWithModuleName !Name.Module FilePath FilePath
  | Elaboration !Scope.KeyedName !Error.Spanned
  deriving (Eq, Show)

data Elaboration
  = NotInScope !Name.Pre
  | Ambiguous !Name.Pre (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | TypeMismatch (Tsil (PrettyableTerm, PrettyableTerm))
  | OccursCheck (Tsil (PrettyableTerm, PrettyableTerm))
  | UnsolvedMetaVariable !Meta.Index !PrettyableTerm
  | NonExhaustivePatterns ![[(Plicity, PrettyablePattern)]]
  | RedundantMatch !MatchKind
  | IndeterminateIndexUnification !MatchKind
  | PlicityMismatch !FieldOrArgument !PlicityMismatch
  | UnableToInferImplicitLambda
  | ImplicitApplicationMismatch (HashSet Name) !PrettyableTerm !PrettyableTerm
  deriving (Eq, Show)

data PlicityMismatch
  = Mismatch !Plicity !Plicity
  | Missing !Plicity
  | Extra
  deriving (Eq, Show)

data FieldOrArgument
  = Field
  | Argument
  deriving (Eq, Show)

instance Pretty FieldOrArgument where
  pretty fieldOrArg =
    case fieldOrArg of
      Field ->
        "field"

      Argument ->
        "argument"

data MatchKind
  = Clause
  | Branch
  | Lambda
  deriving (Eq, Show)

instance Pretty MatchKind where
  pretty clauseOrPat =
    case clauseOrPat of
      Clause ->
        "clause"

      Branch ->
        "branch"

      Lambda ->
        "lambda"

data Spanned
  = Spanned !Span.Relative !Error.Elaboration
  deriving (Eq, Show)

data V

data PrettyableTerm = PrettyableTerm Name.Module [Name] (Syntax.Term V)
  deriving (Eq, Show)

data PrettyablePattern = PrettyablePattern Name.Module [Name] Pattern
  deriving (Eq, Show)
