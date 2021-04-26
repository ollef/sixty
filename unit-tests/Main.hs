{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.IntSeq.Properties
import qualified Hedgehog
import qualified Hedgehog.Main as Hedgehog
import Protolude

main :: IO ()
main =
  Hedgehog.defaultMain
    [ Hedgehog.checkParallel $ Hedgehog.Group "Data.IntSeq" Data.IntSeq.Properties.properties
    ]
