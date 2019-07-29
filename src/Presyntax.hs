{-# language DeriveGeneric #-}
{-# language DeriveAnyClass #-}
module Presyntax where

import Protolude hiding (Type)

import Data.HashMap.Lazy (HashMap)

import qualified Error
import Name (Name)
import qualified Name
import Plicity
import qualified Position
import qualified Scope
import qualified Span

data Term
  = Term !Span.Relative !UnspannedTerm
  deriving (Show, Generic, Hashable)

unspanned :: Term -> UnspannedTerm
unspanned (Term _ term) =
  term

data UnspannedTerm
  = Var !Name.Pre
  | Let !Name !Term !Term
  | Pi !Name !Plicity !Type !Type
  | Fun !Type !Type
  | Lam !PlicitPattern !Term
  | App !Term !Term
  | ImplicitApps !Term (HashMap Name Term)
  | Case !Term [(Pattern, Term)]
  | Wildcard
  | ParseError !Error.Parsing
  deriving (Show, Generic, Hashable)

type Type = Term

data Pattern
  = Pattern !Span.Relative !UnspannedPattern
  deriving (Show, Generic, Hashable)

data UnspannedPattern
  = ConOrVar !Name.Pre [PlicitPattern]
  | WildcardPattern
  | Anno !Pattern !Type
  | Forced !Term
  deriving (Show, Generic, Hashable)

data PlicitPattern
  = ExplicitPattern Pattern
  | ImplicitPattern !Span.Relative (HashMap Name Pattern)
  deriving (Show, Generic, Hashable)

plicitPatternSpan :: PlicitPattern -> Span.Relative
plicitPatternSpan pat =
  case pat of
    ExplicitPattern (Pattern span _) ->
      span

    ImplicitPattern span _ ->
      span

app :: Term -> Term -> Term
app fun@(Term span1 _) arg@(Term span2 _) =
  Term (Span.add span1 span2) $ App fun arg

apps :: Foldable f => Term -> f (Span.Relative, Either (HashMap Name Term) Term) -> Term
apps fun@(Term funSpan _) =
  foldl (\fun' (argSpan, arg) -> Term (Span.add funSpan argSpan) $ either (ImplicitApps fun') (App fun') arg) fun

lams :: Foldable f => f (Position.Relative, PlicitPattern) -> Term -> Term
lams vs body@(Term (Span.Relative _ end) _) =
  foldr (\(start, pat) -> Term (Span.Relative start end) . Lam pat) body vs

pis :: Foldable f => Plicity -> f (Position.Relative, Name) -> Type -> Type -> Type
pis plicity vs source domain@(Term (Span.Relative _ end) _) =
  foldr (\(start, v) -> Term (Span.Relative start end) . Pi v plicity source) domain vs

function :: Term -> Term -> Term
function source@(Term span1 _) domain@(Term span2 _) =
  Term (Span.add span1 span2) $ Fun source domain

anno :: Pattern -> Type -> Pattern
anno pat@(Pattern span1 _) type_@(Term span2 _) =
  Pattern (Span.add span1 span2) (Anno pat type_)

data Definition
  = TypeDeclaration !Type
  | ConstantDefinition [Clause]
  | DataDefinition [(Name, Type, Plicity)] [([Name.Constructor], Type)]
  deriving (Show, Generic, Hashable)

data Clause = Clause
  { _span :: !Span.Relative
  , _patterns :: [PlicitPattern]
  , _rhs :: !Term
  } deriving (Show, Generic, Hashable)

key :: Definition -> Scope.Key
key def =
  case def of
    TypeDeclaration {} ->
      Scope.Type

    ConstantDefinition {} ->
      Scope.Definition

    DataDefinition {} ->
      Scope.Definition
