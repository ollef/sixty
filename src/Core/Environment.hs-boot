{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

module Core.Environment where

import qualified Data.Kind

type role Environment phantom
data Environment (v :: Data.Kind.Type)
