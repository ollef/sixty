{-# LANGUAGE OverloadedStrings #-}

module Core.Domain.Telescope where

import Core.Binding (Binding)
import qualified Core.Domain as Domain
import Monad
import Plicity
import Protolude

data Telescope base
  = Empty !base
  | Extend !Binding !Domain.Type !Plicity (Domain.Value -> M (Telescope base))

apply :: Telescope k -> [(Plicity, Domain.Value)] -> M (Telescope k)
apply tele args =
  case (tele, args) of
    (_, []) ->
      pure tele
    (Extend _ _ plicity1 teleFun, (plicity2, arg) : args')
      | plicity1 == plicity2 -> do
          tele' <- teleFun arg
          apply tele' args'
    _ ->
      panic "Core.Domain.Telescope.apply"
