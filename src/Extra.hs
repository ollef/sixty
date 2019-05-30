module Extra where

import Protolude

import Data.Graph
import qualified Data.HashSet as HashSet

unique :: (Eq a, Hashable a, Foldable f) => f a -> Bool
unique = go mempty . toList
  where
    go seen as =
      case as of
        [] ->
          True

        a:as'
          | a `HashSet.member` seen ->
            False

          | otherwise ->
            go (HashSet.insert a seen) as'

topoSortWith
  :: (Foldable t, Foldable t', Ord name)
  => (a -> name)
  -> (a -> t' name)
  -> t a
  -> [SCC a]
topoSortWith name deps as
  = stronglyConnComp [(a, name a, toList $ deps a) | a <- toList as]
