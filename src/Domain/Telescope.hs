{-# language OverloadedStrings #-}
module Domain.Telescope where

import Protolude

import qualified Domain
import Monad
import Name (Name)
import Plicity

data Telescope t k
  = Empty !k
  | Extend !Name !t !Plicity (Lazy Domain.Value -> M (Telescope t k))

apply :: Telescope t k -> [(Plicity, Lazy Domain.Value)] -> M (Telescope t k)
apply tele args =
  case (tele, args) of
    (_, []) ->
      pure tele

    (Extend _ _ plicity1 teleFun, (plicity2, arg):args')
      | plicity1 == plicity2 -> do
        tele' <- teleFun arg
        apply tele' args'

    _ ->
      panic "Domain.Telescope.apply"
