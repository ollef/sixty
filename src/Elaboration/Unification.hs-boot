module Elaboration.Unification where

import  Elaboration.Context.Type
import Monad
import Protolude
import qualified Core.Domain as Domain

equalArgs :: Context v -> Domain.Args -> Domain.Args -> M Bool
