{-# LANGUAGE BlockArguments #-}

module Elaboration.Depth where

import qualified Core.Domain as Domain
import Monad
import Protolude
import qualified Query
import qualified Query.Mapped as Mapped
import Rock

-- | Try to find out which of two heads might refer to the other so we can
-- unfold glued values that are defined later first (see "depth" in
-- https://arxiv.org/pdf/1505.04324.pdf).
compareHeadDepths :: Domain.Head -> Domain.Head -> M Ordering
compareHeadDepths head1 head2 =
  case (head1, head2) of
    (Domain.Global global1, Domain.Global global2) -> do
      global1DependsOn2 <- fetch $ Query.TransitiveDependencies global2 $ Mapped.Query global1
      global2DependsOn1 <- fetch $ Query.TransitiveDependencies global1 $ Mapped.Query global2
      pure case (global1DependsOn2, global2DependsOn1) of
        (Just _, Nothing) -> GT
        (Nothing, Just _) -> LT
        _ -> EQ
    (_, Domain.Global _) -> pure GT
    (Domain.Global _, _) -> pure LT
    (Domain.Var v1, Domain.Var v2) -> pure $ compare v1 v2
    _ -> pure EQ
