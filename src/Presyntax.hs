{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language LambdaCase #-}
module Presyntax where

import Protolude hiding (Type)

import Data.HashMap.Lazy (HashMap)
import Data.Persist

import Boxity
import qualified Error.Parsing as Error
import qualified Extra
import Literal (Literal)
import Name (Name)
import qualified Name
import Orphans ()
import Plicity
import qualified Scope
import qualified Span

data Term
  = Term !Span.Relative !UnspannedTerm
  deriving (Eq, Show, Generic, Persist, Hashable)

unspanned :: Term -> UnspannedTerm
unspanned (Term _ term) =
  term

data UnspannedTerm
  = Var !Name.Pre
  | Lit !Literal
  | Let !Name !(Maybe (Span.Relative, Type)) [(Span.Relative, Clause)] !Term
  | Pi !Binding !Plicity !Type !Type
  | Fun !Type !Type
  | Lam !PlicitPattern !Term
  | App !Term !Term
  | ImplicitApps !Term (HashMap Name Term)
  | Case !Term [(Pattern, Term)]
  | Wildcard
  | ParseError !Error.Parsing
  deriving (Eq, Show, Generic, Persist, Hashable)

type Type = Term

data Binding = Binding !Span.Relative !Name
  deriving (Eq, Show, Generic, Persist, Hashable)

data Pattern
  = Pattern !Span.Relative !UnspannedPattern
  deriving (Eq, Show, Generic, Persist, Hashable)

data UnspannedPattern
  = ConOrVar !Span.Relative !Name.Pre [PlicitPattern]
  | WildcardPattern
  | LitPattern !Literal
  | Anno !Pattern !Type
  | Forced !Term
  deriving (Eq, Show, Generic, Persist, Hashable)

data PlicitPattern
  = ExplicitPattern !Pattern
  | ImplicitPattern !Span.Relative (HashMap Name Pattern)
  deriving (Eq, Show, Generic, Persist, Hashable)

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

implicitApp :: Term -> HashMap Name Term -> Span.Relative -> Term
implicitApp fun@(Term funSpan _) args endSpan =
  Term (Span.add funSpan endSpan) $ ImplicitApps fun args

lams :: Foldable f => f PlicitPattern -> Term -> Term
lams vs body@(Term bodySpan _) =
  foldr (\pat -> Term (Span.add (plicitPatternSpan pat) bodySpan) . Lam pat) body vs

pis :: Foldable f => Plicity -> f Binding -> Type -> Type -> Type
pis plicity vs domain target@(Term (Span.Relative _ end) _) =
  foldr (\binding@(Binding (Span.Relative start _) _) -> Term (Span.Relative start end) . Pi binding plicity domain) target vs

function :: Term -> Term -> Term
function domain@(Term span1 _) target@(Term span2 _) =
  Term (Span.add span1 span2) $ Fun domain target

anno :: Pattern -> Type -> Pattern
anno pat@(Pattern span1 _) type_@(Term span2 _) =
  Pattern (Span.add span1 span2) (Anno pat type_)

conOrVar :: Span.Relative -> Name.Pre -> [PlicitPattern] -> Pattern
conOrVar nameSpan name patterns =
  let
    span =
      maybe nameSpan (Span.add nameSpan . plicitPatternSpan) $ Extra.last patterns
  in
  Pattern span $ ConOrVar nameSpan name patterns

case_ :: Span.Relative -> Term -> Span.Relative -> [(Pattern, Term)] -> Term
case_ caseSpan scrutinee ofSpan brs =
  Term (Span.add caseSpan $ maybe ofSpan (\(_, Term span _) -> span) $ Extra.last brs) $ Case scrutinee brs


let_ :: Span.Relative -> Name -> Maybe (Span.Relative, Type) -> [(Span.Relative, Clause)] -> Term -> Term
let_ nameSpan name maybeType clauses rhs@(Term rhsSpan _) =
  Term (Span.add nameSpan rhsSpan) $ Let name maybeType clauses rhs

clause :: [PlicitPattern] -> Span.Relative -> Term -> Clause
clause pats equalsSpan rhs@(Term rhsSpan _) =
  case pats of
    [] ->
      Clause (Span.add equalsSpan rhsSpan) pats rhs

    pat:_ ->
      Clause (Span.add (plicitPatternSpan pat) rhsSpan) pats rhs

data Definition
  = TypeDeclaration !Span.Relative !Type
  | ConstantDefinition [(Span.Relative, Clause)]
  | DataDefinition !Span.Relative !Boxity [(Binding, Type, Plicity)] [ConstructorDefinition]
  deriving (Eq, Show, Generic, Persist, Hashable)

data Clause = Clause
  { _span :: !Span.Relative
  , _patterns :: [PlicitPattern]
  , _rhs :: !Term
  } deriving (Eq, Show, Generic, Persist, Hashable)

data ConstructorDefinition
  = GADTConstructors [(Span.Relative, Name.Constructor)] Type
  | ADTConstructor !Span.Relative Name.Constructor [Type]
  deriving (Eq, Show, Generic, Persist, Hashable)

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
