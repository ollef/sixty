{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Core.Syntax where

import Boxity
import Core.Binding (Binding)
import Core.Bindings (Bindings)
import Data.EnumMap (EnumMap)
import Data.EnumSet (EnumSet)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.OrderedHashMap (OrderedHashMap)
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Index (Index, Scope)
import qualified Index
import Literal (Literal)
import qualified Meta
import qualified Name
import Plicity
import qualified Postponement
import Protolude hiding (Type)
import qualified Span
import Telescope (Telescope)
import qualified Telescope
import Unsafe.Coerce

data Term v
  = Var !(Index v)
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Lit !Literal
  | Meta !Meta.Index
  | PostponedCheck !Postponement.Index !(Term v)
  | Lets !(Lets v)
  | Pi !Binding !(Type v) !Plicity !(Scope Type v)
  | Fun !(Type v) !Plicity !(Type v)
  | Lam !Bindings !(Type v) !Plicity !(Scope Term v)
  | App !(Term v) !Plicity !(Term v)
  | Case !(Term v) !(Type v) (Branches v) !(Maybe (Term v))
  | Spanned !Span.Relative !(Term v)
  deriving (Eq, Show, Generic, Hashable)

type Type = Term

data Branches v
  = ConstructorBranches !Name.Qualified (ConstructorBranches v)
  | LiteralBranches (LiteralBranches v)
  deriving (Eq, Show, Generic, Hashable)

data Lets v
  = LetType !Binding !(Type v) !(Scope Lets v)
  | -- | index must refer to a variable introduced in a LetType in the same Lets block
    Let !Bindings !(Index v) !(Term v) !(Lets v)
  | In !(Term v)
  deriving (Eq, Show, Generic, Hashable)

type ConstructorBranches v =
  OrderedHashMap Name.Constructor ([Span.Relative], Telescope Bindings Type Term v)

type LiteralBranches v =
  OrderedHashMap Literal ([Span.Relative], Term v)

implicitPi :: Binding -> Type v -> Plicity -> Scope Type v -> Type v
implicitPi name type_ plicity =
  Pi name type_ (implicitise plicity)

apps :: (Foldable f) => Term v -> f (Plicity, Term v) -> Term v
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

globalView :: Term v -> Maybe Name.Qualified
globalView term =
  case term of
    Global v ->
      Just v
    Spanned _ term' ->
      globalView term'
    _ ->
      Nothing

varView :: Term v -> Maybe (Index v)
varView term =
  case term of
    Var v ->
      Just v
    Spanned _ term' ->
      varView term'
    _ ->
      Nothing

funs :: (Foldable f) => f (Term v) -> Plicity -> Term v -> Term v
funs args plicity res =
  foldr (`Fun` plicity) res args

succ :: Term v -> Term (Index.Succ v)
succ =
  coerce

fromZero :: Term Index.Zero -> Term v
fromZero =
  coerce

coerce :: Term v -> Term v'
-- Can't be Data.Coerce.coerce anymore due to role limitations for Telescopes
coerce =
  unsafeCoerce

type MetaSolutions =
  EnumMap Meta.Index (Term Index.Zero, Type Index.Zero, EnumSet Meta.Index)

data Definition
  = TypeDeclaration !(Type Index.Zero)
  | ConstantDefinition !(Term Index.Zero)
  | DataDefinition !Boxity !(Telescope Binding Type ConstructorDefinitions Index.Zero)
  deriving (Eq, Show, Generic, Hashable)

newtype ConstructorDefinitions v
  = ConstructorDefinitions (OrderedHashMap Name.Constructor (Type v))
  deriving (Show, Generic)
  deriving newtype (Eq, Hashable)

constructorFieldPlicities :: Type v -> [Plicity]
constructorFieldPlicities type_ =
  case type_ of
    Pi _ _ plicity type' ->
      plicity : constructorFieldPlicities type'
    Fun _ plicity type' ->
      plicity : constructorFieldPlicities type'
    _ ->
      []

dependencies :: Term v -> HashSet Name.Qualified
dependencies term =
  case term of
    Var _ -> mempty
    Global name -> HashSet.singleton name
    Con (Name.QualifiedConstructor name _) -> HashSet.singleton name
    Lit _ -> mempty
    Meta _ -> mempty
    PostponedCheck _ term' -> dependencies term'
    Lets lets -> letsDependencies lets
    Pi _ domain _ target -> dependencies domain <> dependencies target
    Fun domain _ target -> dependencies domain <> dependencies target
    Lam _ type_ _ body -> dependencies type_ <> dependencies body
    App function _ argument -> dependencies function <> dependencies argument
    Case scrutinee type_ branches defaultBranch ->
      dependencies scrutinee
        <> dependencies type_
        <> branchesDependencies branches
        <> foldMap dependencies defaultBranch
    Spanned _ term' -> dependencies term'

letsDependencies :: Lets v -> HashSet Name.Qualified
letsDependencies lets =
  case lets of
    LetType _ type_ lets' -> dependencies type_ <> letsDependencies lets'
    Let _ _ term lets' -> dependencies term <> letsDependencies lets'
    In term -> dependencies term

branchesDependencies :: Branches v -> HashSet Name.Qualified
branchesDependencies branches =
  case branches of
    ConstructorBranches typeName constructorBranches ->
      HashSet.singleton typeName
        <> foldMap (foldMap $ Telescope.foldMap dependencies dependencies) constructorBranches
    LiteralBranches literalBranches -> foldMap (foldMap dependencies) literalBranches

definitionDependencies :: Definition -> HashSet Name.Qualified
definitionDependencies def =
  case def of
    TypeDeclaration type_ -> dependencies type_
    ConstantDefinition term -> dependencies term
    DataDefinition _ constructorDefs ->
      Telescope.foldMap dependencies (\(ConstructorDefinitions cs) -> foldMap dependencies cs) constructorDefs
