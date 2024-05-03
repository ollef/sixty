{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
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
  | Stuck !Head Args !Value Spine
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
  deriving (Show, Eq, Generic, Hashable)

anyNeutralView :: Value -> Maybe (Head, Spine)
anyNeutralView = \case
  Neutral hd spine -> Just (hd, spine)
  Stuck hd args _ spine -> Just (hd, Apps args <> spine)
  _ -> Nothing

pattern AnyNeutral :: Head -> Spine -> Value
pattern AnyNeutral hd spine <- (anyNeutralView -> Just (hd, spine))

{-# COMPLETE AnyNeutral, Con, Lit, Glued, Core.Domain.Lazy, Lam, Pi, Fun #-}

type Environment = Environment.Environment Value

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

data Branches where
  Branches :: Type -> Environment v -> Syntax.Branches v -> Maybe (Syntax.Term v) -> Branches

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

data Spine = Spine Args (Seq (Branches, Args))

type Args = Seq (Plicity, Value)

data Elimination
  = App !Plicity !Value
  | Case !Branches

pattern Empty :: Spine
pattern Empty =
  Spine Seq.Empty Seq.Empty

pattern (:<) :: Elimination -> Spine -> Spine
pattern elimination :< spine <-
  (eliminationViewL -> Just (elimination, spine))
  where
    App plicity arg :< Spine args spine = Spine ((plicity, arg) Seq.:<| args) spine
    Case brs :< Spine args spine = Spine mempty ((brs, args) Seq.:<| spine)

{-# COMPLETE Empty, (:<) #-}

pattern (:>) :: Spine -> Elimination -> Spine
pattern spine :> elimination <-
  (eliminationViewR -> Just (spine, elimination))
  where
    Spine args Seq.Empty :> App plicity arg =
      Spine (args Seq.:|> (plicity, arg)) Seq.Empty
    Spine args (spine Seq.:|> (brs, args')) :> App plicity arg =
      Spine args (spine Seq.:|> (brs, args' Seq.:|> (plicity, arg)))
    Spine args spine :> Case brs = Spine args (spine Seq.:|> (brs, mempty))

{-# COMPLETE Empty, (:>) #-}

pattern Apps :: Seq (Plicity, Value) -> Spine
pattern Apps args = Spine args Seq.Empty

eliminationViewL :: Spine -> Maybe (Elimination, Spine)
eliminationViewL = \case
  Spine ((plicity, arg) Seq.:<| args) spine -> Just (App plicity arg, Spine args spine)
  Spine Seq.Empty ((brs, args) Seq.:<| spine) -> Just (Case brs, Spine args spine)
  Spine Seq.Empty Seq.Empty -> Nothing

eliminationViewR :: Spine -> Maybe (Spine, Elimination)
eliminationViewR = \case
  Spine args (spine Seq.:|> (brs, args' Seq.:|> (plicity, arg))) -> Just (Spine args (spine Seq.:|> (brs, args')), App plicity arg)
  Spine args (spine Seq.:|> (brs, Seq.Empty)) -> Just (Spine args spine, Case brs)
  Spine (args Seq.:|> (plicity, arg)) Seq.Empty -> Just (Spine args Seq.Empty, App plicity arg)
  Spine Seq.Empty Seq.Empty -> Nothing

foldl :: (a -> Elimination -> a) -> a -> Spine -> a
foldl f e spine =
  case spine of
    Empty ->
      e
    spine' :> elim ->
      f (Core.Domain.foldl f e spine') elim

foldlM :: (Monad m) => (a -> Elimination -> m a) -> a -> Spine -> m a
foldlM f e spine =
  case spine of
    Empty ->
      pure e
    spine' :> elim -> do
      a <- Core.Domain.foldlM f e spine'
      f a elim

mapM :: (Monad m) => (Elimination -> m a) -> Spine -> m (Tsil a)
mapM f spine =
  case spine of
    Empty ->
      pure Tsil.Empty
    spine' :> elim -> do
      as <- Core.Domain.mapM f spine'
      a <- f elim
      pure $ as Tsil.:> a

mapM_ :: (Monad m) => (Elimination -> m ()) -> Spine -> m ()
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

matchSpinePrefix :: Spine -> Spine -> Maybe (Spine, Spine)
matchSpinePrefix (Spine sargs srest) (Spine pargs Seq.Empty)
  | Seq.length sargs >= Seq.length pargs = do
      let (prefix, suffix) = Seq.splitAt (Seq.length pargs) sargs
      Just (Spine prefix Seq.Empty, Spine suffix srest)
matchSpinePrefix (Spine sargs ((sbrs, sargs') Seq.:<| srest)) (Spine pargs ((_, pargs') Seq.:<| prest))
  | Seq.length sargs == Seq.length pargs = do
      (Spine prefixArgs prefix, suffix) <- matchSpinePrefix (Spine sargs' srest) (Spine pargs' prest)
      Just (Spine sargs ((sbrs, prefixArgs) Seq.:<| prefix), suffix)
matchSpinePrefix _ _ = Nothing
