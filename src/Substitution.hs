{-# language ScopedTypeVariables #-}
module Substitution where

import Protolude

import Context (Context)
import qualified Context
import qualified Environment
import qualified Index
import qualified Inlining
import Monad
import qualified Syntax

let_ :: Context v -> Syntax.Term v -> Syntax.Term (Index.Succ v) -> M (Syntax.Term v)
let_ context term body = do
  let
    env =
      createEnvironment context
  value <- Inlining.evaluate (const False) env term
  (env', _) <- Environment.extendValue env value
  bodyValue <- Inlining.evaluate (const False) env' body
  pure $ Inlining.readback env bodyValue

createEnvironment :: Context v -> Inlining.Environment v
createEnvironment context =
  (Context.toEnvironment context) { Environment.values = mempty }
