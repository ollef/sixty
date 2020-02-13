module HashTag where

import Protolude

-- | Hash the result of a @k@ query.
--
-- A typical implementation looks like:
--
-- @
-- data Query a where
--   ReadFile :: 'FilePath' -> Query 'Text'
--
-- instance 'HashTag' Query where
--   'hashTagged' query =
--     case query of
--       ReadFile {} -> 'hash'
-- @
class HashTag k where
  hashTagged :: k a -> a -> Int
