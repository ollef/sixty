{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module Surface.Syntax where

import Boxity
import Data.HashMap.Lazy (HashMap)
import Data.Persist
import qualified Error.Parsing as Error
import qualified Extra
import Literal (Literal)
import Name (Name)
import qualified Name
import Orphans ()
import Plicity
import Protolude hiding (Type)
import qualified Scope
import qualified Span

data Term
  = Term !Span.Relative !UnspannedTerm
  deriving (Eq, Show, Generic, Persist, Hashable)

unspanned :: Term -> UnspannedTerm
unspanned (Term _ term) =
  term

data UnspannedTerm
  = Var !Name.Surface
  | Lit !Literal
  | Lets [Let] !Term
  | Pi !SpannedName !Plicity !Type !Type
  | Fun !Type !Type
  | Lam !PlicitPattern !Term
  | App !Term !Term
  | ImplicitApps !Term (HashMap Name Term)
  | Case !Term [(Pattern, Term)]
  | Wildcard
  | ParseError !Error.Parsing
  deriving (Eq, Show, Generic, Persist, Hashable)

type Type = Term

data Let
  = LetType !SpannedName !Type
  | Let !Name.Surface [(Span.Relative, Clause)]
  deriving (Eq, Show, Generic, Persist, Hashable)

data SpannedName = SpannedName !Span.Relative !Name.Surface
  deriving (Eq, Show, Generic, Persist, Hashable)

data Pattern
  = Pattern !Span.Relative !UnspannedPattern
  deriving (Eq, Show, Generic, Persist, Hashable)

data UnspannedPattern
  = ConOrVar !SpannedName [PlicitPattern]
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

lams :: Foldable f => Span.Relative -> f PlicitPattern -> Term -> Term
lams span vs body@(Term bodySpan _) =
  Term (Span.add span outerSpan) result
  where
    Term outerSpan result =
      foldr (\pat -> Term (Span.add (plicitPatternSpan pat) bodySpan) . Lam pat) body vs

pis :: Plicity -> [(Span.Relative, [SpannedName], Type)] -> Type -> Type
pis plicity vars target@(Term (Span.Relative _ end) _) =
  foldr
    ( \(span, vs, domain) target' -> do
        let Term outerSpan result =
              foldr (\spannedName@(SpannedName (Span.Relative start _) _) -> Term (Span.Relative start end) . Pi spannedName plicity domain) target' vs
        Term (Span.add span outerSpan) result
    )
    target
    vars

implicitPis :: Span.Relative -> [(Span.Relative, [SpannedName], Type)] -> Type -> Type
implicitPis forallSpan vars target =
  Term (Span.add forallSpan outerSpan) result
  where
    Term outerSpan result =
      pis Implicit vars target

function :: Term -> Term -> Term
function domain@(Term span1 _) target@(Term span2 _) =
  Term (Span.add span1 span2) $ Fun domain target

anno :: Pattern -> Type -> Pattern
anno pat@(Pattern span1 _) type_@(Term span2 _) =
  Pattern (Span.add span1 span2) (Anno pat type_)

conOrVar :: SpannedName -> [PlicitPattern] -> Pattern
conOrVar spannedName@(SpannedName nameSpan _) patterns =
  let span =
        maybe nameSpan (Span.add nameSpan . plicitPatternSpan) $ Extra.last patterns
   in Pattern span $ ConOrVar spannedName patterns

case_ :: Span.Relative -> Term -> Span.Relative -> [(Pattern, Term)] -> Term
case_ caseSpan scrutinee ofSpan brs =
  Term (Span.add caseSpan $ maybe ofSpan (\(_, Term span _) -> span) $ Extra.last brs) $ Case scrutinee brs

lets :: Span.Relative -> [Let] -> Term -> Term
lets letSpan ls rhs@(Term rhsSpan _) =
  Term (Span.add letSpan rhsSpan) (Lets ls rhs)

clause :: [PlicitPattern] -> Span.Relative -> Term -> Clause
clause pats equalsSpan rhs@(Term rhsSpan _) =
  case pats of
    [] ->
      Clause (Span.add equalsSpan rhsSpan) pats rhs
    pat : _ ->
      Clause (Span.add (plicitPatternSpan pat) rhsSpan) pats rhs

data Definition
  = TypeDeclaration !Span.Relative !Type
  | ConstantDefinition [(Span.Relative, Clause)]
  | DataDefinition !Span.Relative !Boxity [(SpannedName, Type, Plicity)] [ConstructorDefinition]
  deriving (Eq, Show, Generic, Persist, Hashable)

data Clause = Clause
  { _span :: !Span.Relative
  , _patterns :: [PlicitPattern]
  , _rhs :: !Term
  }
  deriving (Eq, Show, Generic, Persist, Hashable)

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

entityKind :: Definition -> Scope.EntityKind
entityKind def = case def of
  TypeDeclaration {} -> Scope.Type
  ConstantDefinition {} -> Scope.Definition
  DataDefinition {} -> Scope.Definition
