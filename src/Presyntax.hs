{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language LambdaCase #-}
module Presyntax where

import Protolude hiding (Type)

import Data.HashMap.Lazy (HashMap)

import Boxity
import qualified Error.Parsing as Error
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
  | Int !Integer
  | Let !Name !(Maybe (Span.Relative, Type)) [(Span.Relative, Clause)] !Term
  | Pi !Binding !Plicity !Type !Type
  | Fun !Type !Type
  | Lam !PlicitPattern !Term
  | App !Term !Term
  | ImplicitApps !Term (HashMap Name Term)
  | Case !Term [(Pattern, Term)]
  | Wildcard
  | ParseError !Error.Parsing
  deriving (Show, Generic, Hashable)

type Type = Term

data Binding = Binding !Span.Relative !Name
  deriving (Show, Generic, Hashable)

data Pattern
  = Pattern !Span.Relative !UnspannedPattern
  deriving (Show, Generic, Hashable)

data UnspannedPattern
  = ConOrVar !Span.Relative !Name.Pre [PlicitPattern]
  | WildcardPattern
  | IntPattern !Integer
  | Anno !Pattern !Type
  | Forced !Term
  deriving (Show, Generic, Hashable)

data PlicitPattern
  = ExplicitPattern !Pattern
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

pis :: Foldable f => Plicity -> f Binding -> Type -> Type -> Type
pis plicity vs domain target@(Term (Span.Relative _ end) _) =
  foldr (\binding@(Binding (Span.Relative start _) _) -> Term (Span.Relative start end) . Pi binding plicity domain) target vs

function :: Term -> Term -> Term
function domain@(Term span1 _) target@(Term span2 _) =
  Term (Span.add span1 span2) $ Fun domain target

anno :: Pattern -> Type -> Pattern
anno pat@(Pattern span1 _) type_@(Term span2 _) =
  Pattern (Span.add span1 span2) (Anno pat type_)

data Definition
  = TypeDeclaration !Span.Relative !Type
  | ConstantDefinition [(Span.Relative, Clause)]
  | DataDefinition !Span.Relative !Boxity [(Binding, Type, Plicity)] [ConstructorDefinition]
  deriving (Show, Generic, Hashable)

data Clause = Clause
  { _span :: !Span.Relative
  , _patterns :: [PlicitPattern]
  , _rhs :: !Term
  } deriving (Show, Generic, Hashable)

data ConstructorDefinition
  = GADTConstructors [(Span.Relative, Name.Constructor)] Type
  | ADTConstructor !Span.Relative Name.Constructor [Type]
  deriving (Show, Generic, Hashable)

spans :: Definition -> [Span.Relative]
spans def =
  case def of
    TypeDeclaration span _ ->
      [span]

    ConstantDefinition clauses ->
      fst <$> clauses

    DataDefinition span _ _ _ ->
      [span]

constructorSpans :: Definition -> [(Span.Relative, Name.Constructor)]
constructorSpans def =
  case def of
    TypeDeclaration _ _ ->
      []

    ConstantDefinition _ ->
      []

    DataDefinition _ _ _ constrDefs ->
      constrDefs >>= \case
        GADTConstructors cs _ ->
          cs

        ADTConstructor span constr _ ->
          [(span, constr)]

key :: Definition -> Scope.Key
key def =
  case def of
    TypeDeclaration {} ->
      Scope.Type

    ConstantDefinition {} ->
      Scope.Definition

    DataDefinition {} ->
      Scope.Definition
