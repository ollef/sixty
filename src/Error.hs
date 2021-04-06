{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Error where

import Core.Domain.Pattern (Pattern)
import qualified Core.Syntax as Syntax
import Data.HashSet (HashSet)
import Data.Persist
import Data.Text.Prettyprint.Doc
import Data.Tsil (Tsil)
import qualified Error.Parsing as Error
import qualified Meta
import qualified Module
import Name (Name)
import qualified Name
import Plicity
import Protolude
import qualified Scope
import qualified Span

data Error
  = Parse FilePath !Error.Parsing
  | DuplicateName !Scope.KeyedName !Span.Absolute
  | ImportNotFound !Name.Module !Module.Import
  | MultipleFilesWithModuleName !Name.Module FilePath FilePath
  | ModuleFileNameMismatch !Name.Module !Name.Module !Span.Absolute FilePath
  | Elaboration !Scope.KeyedName !Error.Spanned
  deriving (Eq, Show, Generic, Persist)

data Elaboration
  = NotInScope !Name.Surface
  | Ambiguous !Name.Surface (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | DuplicateLetName !Name.Surface !Span.Relative
  | UndefinedLetName !Name.Surface
  | TypeMismatch (Tsil (PrettyableTerm, PrettyableTerm))
  | OccursCheck (Tsil (PrettyableTerm, PrettyableTerm))
  | UnsolvedMetaVariable !Meta.Index !PrettyableTerm
  | NonExhaustivePatterns ![[(Plicity, PrettyablePattern)]]
  | RedundantMatch !MatchKind
  | IndeterminateIndexUnification !MatchKind
  | PlicityMismatch !FieldOrArgument !PlicityMismatch
  | UnableToInferImplicitLambda
  | ImplicitApplicationMismatch (HashSet Name) !PrettyableTerm !PrettyableTerm
  deriving (Eq, Show, Generic, Persist, Exception)

data PlicityMismatch
  = Mismatch !Plicity !Plicity
  | Missing !Plicity
  | Extra
  deriving (Eq, Show, Generic, Persist)

data FieldOrArgument
  = Field
  | Argument
  deriving (Eq, Show, Generic, Persist)

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
  deriving (Eq, Show, Generic, Persist)

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
  deriving (Eq, Show, Generic, Persist)

data V

data PrettyableTerm = PrettyableTerm Name.Module [Name] (Syntax.Term V)
  deriving (Eq, Show, Generic, Persist)

data PrettyablePattern = PrettyablePattern Name.Module [Name] Pattern
  deriving (Eq, Show, Generic, Persist)
