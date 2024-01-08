{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Core.Domain where

import Core.Binding (Binding)
import Core.Bindings (Bindings)
import qualified Core.Syntax as Syntax
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Flexibility (Flexibility)
import qualified Flexibility
import Index
import Literal (Literal)
import qualified Meta
import Monad
import qualified Name
import Plicity
import Protolude hiding (IntMap, Seq, Type)
import Var (Var)

data Value
  = Neutral !Head Spine
  | Con !Name.QualifiedConstructor (Tsil (Plicity, Value))
  | Lit !Literal
  | Glued !Head Spine !Value
  | Lazy !(Lazy Value)
  | Lam !Bindings !Type !Plicity !Closure
  | Pi !Binding !Type !Plicity !Closure
  | Fun !Type !Plicity !Type

type Type = Value

data Head
  = Var !Var
  | Global !Name.Qualified
  | Meta !Meta.Index
  deriving (Show, Eq)

type Environment = Environment.Environment Value

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

data Branches where
  Branches :: Environment v -> Syntax.Branches v -> Maybe (Syntax.Term v) -> Branches

var :: Var -> Value
var v = Neutral (Var v) mempty

global :: Name.Qualified -> Value
global g = Neutral (Global g) mempty

con :: Name.QualifiedConstructor -> Value
con c = Con c mempty

meta :: Meta.Index -> Value
meta i = Neutral (Meta i) mempty

singleVarView :: Value -> Maybe Var
singleVarView (Neutral (Var v) Empty) = Just v
singleVarView _ = Nothing

headFlexibility :: Head -> Flexibility
headFlexibility = \case
  Var _ ->
    Flexibility.Rigid
  Global _ ->
    Flexibility.Rigid
  Meta _ ->
    Flexibility.Flexible

-------------------------------------------------------------------------------

-- * Elimination spines

data Spine = Spine (Seq (Args, Branches)) Args

type Args = Seq (Plicity, Value)

data Elimination
  = App !Plicity !Value
  | Case !Branches

pattern Empty :: Spine
pattern Empty =
  Spine Seq.Empty Seq.Empty

pattern (:>) :: Spine -> Elimination -> Spine
pattern spine :> elimination <-
  (eliminationView -> Just (spine, elimination))
  where
    Spine spine args :> elim =
      case elim of
        App plicity arg ->
          Spine spine (args Seq.:|> (plicity, arg))
        Case brs ->
          Spine (spine Seq.:|> (args, brs)) Seq.Empty

{-# COMPLETE Empty, (:>) #-}

pattern Apps :: Seq (Plicity, Value) -> Spine
pattern Apps args <-
  (appsView -> Just args)
  where
    Apps args =
      Spine Seq.Empty args

eliminationView :: Spine -> Maybe (Spine, Elimination)
eliminationView (Spine spine apps) =
  case apps of
    Seq.Empty ->
      case spine of
        Seq.Empty ->
          Nothing
        spine' Seq.:|> (apps', brs) ->
          Just (Spine spine' apps', Case brs)
    apps' Seq.:|> (plicity, arg) ->
      Just (Spine spine apps', App plicity arg)

appsView :: Spine -> Maybe (Seq (Plicity, Value))
appsView (Spine spine args) =
  case spine of
    Seq.Empty ->
      Just args
    _ ->
      Nothing

foldl :: (a -> Elimination -> a) -> a -> Spine -> a
foldl f e spine =
  case spine of
    Empty ->
      e
    spine' :> elim ->
      f (Core.Domain.foldl f e spine') elim

foldlM :: Monad m => (a -> Elimination -> m a) -> a -> Spine -> m a
foldlM f e spine =
  case spine of
    Empty ->
      pure e
    spine' :> elim -> do
      a <- Core.Domain.foldlM f e spine'
      f a elim

mapM :: Monad m => (Elimination -> m a) -> Spine -> m (Tsil a)
mapM f spine =
  case spine of
    Empty ->
      pure Tsil.Empty
    spine' :> elim -> do
      as <- Core.Domain.mapM f spine'
      a <- f elim
      pure $ as Tsil.:> a

mapM_ :: Monad m => (Elimination -> m ()) -> Spine -> m ()
mapM_ f spine =
  case spine of
    Empty ->
      pure ()
    spine' :> elim -> do
      Core.Domain.mapM_ f spine'
      f elim

instance Semigroup Spine where
  spine1 <> Empty = spine1
  spine1 <> spine2 :> elim = (spine1 <> spine2) :> elim

instance Monoid Spine where
  mempty = Empty
