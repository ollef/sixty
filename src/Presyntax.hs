{-# language DeriveGeneric #-}
{-# language DeriveAnyClass #-}
module Presyntax where

import Protolude hiding (Type)

import qualified Error
import Name (Name)
import qualified Name
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
  | Let !Name.Name !Term !Term
  | Pi !Name.Name !Type !Type
  | Fun !Type !Type
  | Lam !Name.Name !Term
  | App !Term !Term
  | Wildcard
  | ParseError !Error.Parsing
  deriving (Show, Generic, Hashable)

type Type = Term

app :: Term -> Term -> Term
app fun@(Term (Span.Relative start _) _) arg@(Term (Span.Relative _ end) _) =
  Term (Span.Relative start end) $ App fun arg

apps :: Foldable f => Term -> f Term -> Term
apps fun@(Term (Span.Relative start _) _) =
  foldl (\fun' arg@(Term (Span.Relative _ end) _) -> Term (Span.Relative start end) $ App fun' arg) fun

lam :: (Position.Relative, Name.Name) -> Term -> Term
lam (start, v) body@(Term (Span.Relative _ end) _) =
  Term (Span.Relative start end) $ Lam v body

lams :: Foldable f => f (Position.Relative, Name.Name) -> Term -> Term
lams vs body@(Term (Span.Relative _ end) _) =
  foldr (\(start, v) -> Term (Span.Relative start end) . Lam v) body vs

pi :: (Position.Relative, Name.Name) -> Type -> Type -> Type
pi (start, v) source domain@(Term (Span.Relative _ end) _) =
  Term (Span.Relative start end) $ Pi v source domain

pis :: Foldable f => f (Position.Relative, Name.Name) -> Type -> Type -> Type
pis vs source domain@(Term (Span.Relative _ end) _) =
  foldr (\(start, v) -> Term (Span.Relative start end) . Pi v source) domain vs

function :: Term -> Term -> Term
function source@(Term (Span.Relative start _) _) domain@(Term (Span.Relative _ end) _) =
  Term (Span.Relative start end) $ Fun source domain

data Definition
  = TypeDeclaration !Type
  | ConstantDefinition !Term
  | DataDefinition [(Name.Name, Type)] [(Name.Constructor, Type)]
  deriving (Show, Generic, Hashable)

key :: Definition -> Scope.Key
key def =
  case def of
    TypeDeclaration {} ->
      Scope.Type

    ConstantDefinition {} ->
      Scope.Definition

    DataDefinition {} ->
      Scope.Definition
