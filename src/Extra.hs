module Extra where

import Protolude

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
