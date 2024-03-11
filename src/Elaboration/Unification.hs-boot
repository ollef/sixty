module Elaboration.Unification where

import qualified Core.Domain as Domain
import Elaboration.Context.Type
import Monad
import Protolude

equalSpines :: Context v -> Domain.Spine -> Domain.Spine -> M Bool
