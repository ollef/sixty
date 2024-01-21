module Elaboration.Unification where

import  Elaboration.Context.Type
import Monad
import Protolude
import qualified Core.Domain as Domain

equalSpines :: Context v -> Domain.Spine -> Domain.Spine -> M Bool
