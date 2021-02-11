{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Core.Syntax where

import Protolude hiding (Type, IntMap)

import Data.OrderedHashMap (OrderedHashMap)
import Data.Persist
import Unsafe.Coerce

import Boxity
import Core.Binding (Binding)
import Core.Bindings (Bindings)
import Data.IntMap (IntMap)
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Index
import Literal (Literal)
import qualified Meta
import qualified Name
import Plicity
import qualified Postponement
import qualified Span
import Telescope (Telescope)

data Term v
  = Var !(Index v)
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Lit !Literal
  | Meta !Meta.Index
  | PostponedCheck !Postponement.Index !(Term v)
  | Let !Bindings !(Term v) !(Type v) !(Scope Term v)
  | Pi !Binding !(Type v) !Plicity !(Scope Type v)
  | Fun !(Type v) !Plicity !(Type v)
  | Lam !Bindings !(Type v) !Plicity !(Scope Term v)
  | App !(Term v) !Plicity !(Term v)
  | Case !(Term v) (Branches v) !(Maybe (Term v))
  | Spanned !Span.Relative !(Term v)
  deriving (Eq, Show, Generic, Persist, Hashable)

type Type = Term

data Branches v
  = ConstructorBranches !Name.Qualified (ConstructorBranches v)
  | LiteralBranches (LiteralBranches v)
  deriving (Eq, Show, Generic, Persist, Hashable)

type ConstructorBranches v =
  OrderedHashMap Name.Constructor ([Span.Relative], Telescope Bindings Type Term v)

type LiteralBranches v =
  OrderedHashMap Literal ([Span.Relative], Term v)

implicitPi :: Binding -> Type v -> Plicity -> Scope Type v -> Type v
implicitPi name type_ plicity =
  Pi name type_ (implicitise plicity)

apps :: Foldable f => Term v -> f (Plicity, Term v) -> Term v
apps =
  foldl (\fun (plicity, arg) -> App fun plicity arg)

appsView :: Term v -> (Term v, Tsil (Plicity, Term v))
appsView term =
  case term of
    App t1 plicity t2 ->
      second (Tsil.:> (plicity, t2)) $ appsView t1

    Spanned span term' ->
      case appsView term' of
        (hd, Tsil.Empty) ->
          (Spanned span hd, Tsil.Empty)

        result ->
          result

    _ ->
      (term, mempty)

varView :: Term v -> Maybe (Index v)
varView term =
  case term of
    Var v ->
      Just v

    Spanned _ term' ->
      varView term'

    _ ->
      Nothing

funs :: Foldable f => f (Term v) -> Plicity -> Term v -> Term v
funs args plicity res =
  foldr (\a b -> Fun a plicity b) res args

succ :: Term v -> Term (Succ v)
succ =
  coerce

fromVoid :: Term Void -> Term v
fromVoid =
  coerce

coerce :: Term v -> Term v'
-- Can't be Data.Coerce.coerce anymore due to role limitations for Telescopes
coerce =
  unsafeCoerce

type MetaSolutions =
  IntMap Meta.Index (Term Void, Type Void)

data Definition
  = TypeDeclaration !(Type Void)
  | ConstantDefinition !(Term Void)
  | DataDefinition !Boxity !(Telescope Binding Type ConstructorDefinitions Void)
  deriving (Eq, Show, Generic, Persist, Hashable)

newtype ConstructorDefinitions v =
  ConstructorDefinitions (OrderedHashMap Name.Constructor (Type v))
  deriving (Eq, Show, Generic, Persist, Hashable)

constructorFieldPlicities :: Type v -> [Plicity]
constructorFieldPlicities type_ =
  case type_ of
    Pi _ _ plicity type' ->
      plicity : constructorFieldPlicities type'

    Fun _ plicity type' ->
      plicity : constructorFieldPlicities type'

    _ ->
      []
