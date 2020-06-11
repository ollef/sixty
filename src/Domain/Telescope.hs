{-# language OverloadedStrings #-}
module Domain.Telescope where

import Protolude

import qualified Domain
import Monad
import Plicity

data Telescope name type_ base
  = Empty !base
  | Extend !name !type_ !Plicity (Domain.Value -> M (Telescope name type_ base))

apply :: Telescope n t k -> [(Plicity, Domain.Value)] -> M (Telescope n t k)
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
