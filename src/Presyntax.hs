{-# language DeriveGeneric #-}
{-# language DeriveAnyClass #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
module Presyntax where

import Protolude hiding (Type)

import qualified Name
import qualified Position
import qualified Span

newtype Name = Name Text
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable, IsString)

data Term
  = Term !Span.Relative !UnspannedTerm
  deriving (Show, Generic, Hashable)

unspanned :: Term -> UnspannedTerm
unspanned (Term _ term) =
  term

data UnspannedTerm
  = Var !Name
  | Let !Name.Name !Term !Term
  | Pi !Name.Name !Type !Type
  | Fun !Type !Type
  | Lam !Name.Name !Term
  | App !Term !Term
  | Wildcard
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
  = TypeDeclaration !Name.Name !Type
  | ConstantDefinition !Name.Name !Term
  deriving (Show, Generic, Hashable)

definitionName :: Definition -> Name.Name
definitionName def =
  case def of
    TypeDeclaration name _ -> name
    ConstantDefinition name _ -> name
