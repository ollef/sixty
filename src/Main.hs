module Main where

import Protolude

import qualified Parser

main :: IO ()
main = do
  [x] <- getArgs
  Parser.parseTest Parser.term x

