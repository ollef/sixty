{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}
module Data.Tsil where

import Protolude

data Tsil a
  = Nil
  | Snoc (Tsil a) a
  deriving (Eq, Functor, Ord, Show, Traversable)

instance Semigroup (Tsil a) where
  xs <> Nil = xs
  xs <> Snoc ys y = Snoc (xs <> ys) y

instance Monoid (Tsil a) where
  mempty = Nil
  mappend = (<>)

instance Applicative Tsil where
  pure = Snoc Nil
  (<*>) = ap

instance Alternative Tsil where
  empty = Nil
  (<|>) = mappend

instance Monad Tsil where
  return = pure
  Nil >>= _ = Nil
  Snoc xs x >>= f = (xs >>= f) <> f x

fromList :: [a] -> Tsil a
fromList = foldr (flip Snoc) Nil . reverse

instance Foldable Tsil where
  foldMap _ Nil = mempty
  foldMap f (Snoc xs x) = foldMap f xs `mappend` f x

  toList = reverse . go
    where
      go Nil = []
      go (Snoc xs x) = x : go xs

lookup :: Eq a => a -> Tsil (a, b) -> Maybe b
lookup _ Nil = Nothing
lookup a (Snoc as (a', b))
  | a == a' = Just b
  | otherwise = Data.Tsil.lookup a as

filter :: (a -> Bool) -> Tsil a -> Tsil a
filter _ Nil = Nil
filter f (Snoc xs x)
  | f x = Snoc (Data.Tsil.filter f xs) x
  | otherwise = Data.Tsil.filter f xs

span :: (a -> Bool) -> Tsil a -> (Tsil a, Tsil a)
span _ Nil = (Nil, Nil)
span p as@(Snoc as' a)
  | p a = second (`Snoc` a) $ span p as'
  | otherwise = (as, Nil)

zip :: Tsil a -> Tsil b -> Tsil (a, b)
zip = Data.Tsil.zipWith (,)

zipWith :: (a -> b -> c) -> Tsil a -> Tsil b -> Tsil c
zipWith _ Nil _ = Nil
zipWith _ _ Nil = Nil
zipWith f (Snoc as a) (Snoc bs b) = Snoc (Data.Tsil.zipWith f as bs) (f a b)

zipWithM :: Monad m => (a -> b -> m c) -> Tsil a -> Tsil b -> m (Tsil c)
zipWithM f as bs = sequenceA (Data.Tsil.zipWith f as bs)

zipWithM_ :: Monad m => (a -> b -> m c) -> Tsil a -> Tsil b -> m ()
zipWithM_ f as bs = sequenceA_ (Data.Tsil.zipWith f as bs)

unzip :: Tsil (a, b) -> (Tsil a, Tsil b)
unzip Nil = (Nil, Nil)
unzip (Snoc as (a, b)) = (Snoc as' a, Snoc bs' b)
  where
    (as', bs') = Data.Tsil.unzip as
