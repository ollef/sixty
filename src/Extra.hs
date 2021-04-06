module Extra where

import Data.Graph
import qualified Data.HashSet as HashSet
import Protolude

unique :: (Eq a, Hashable a, Foldable f) => f a -> Bool
unique = go mempty . toList
  where
    go seen as =
      case as of
        [] ->
          True
        a : as'
          | a `HashSet.member` seen ->
            False
          | otherwise ->
            go (HashSet.insert a seen) as'

topoSortWith ::
  (Foldable t, Ord name) =>
  (a -> name) ->
  (a -> [name]) ->
  t a ->
  [SCC a]
topoSortWith name deps as =
  stronglyConnComp [(a, name a, deps a) | a <- toList as]

last :: [a] -> Maybe a
last =
  go Nothing
  where
    go result as =
      case as of
        [] ->
          result
        a : as' ->
          go (Just a) as'

{-# INLINE defaultHashWithSalt #-}
defaultHashWithSalt :: Hashable a => Int -> a -> Int
defaultHashWithSalt salt x =
  salt `combine` hash x
  where
    {-# INLINE combine #-}
    combine :: Int -> Int -> Int
    combine h1 h2 =
      (h1 * 16777619) `xor` h2
