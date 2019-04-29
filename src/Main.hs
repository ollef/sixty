{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Protolude hiding (force)

import qualified Text.Parsix as Parsix

import qualified Context
import qualified Elaboration
import Monad
import qualified Parser
import qualified Readback

main :: IO ()
main = do
  [inputString] <- getArgs
  parseAndTypeCheck inputString

parseAndTypeCheck :: StringConv s Text => s -> IO ()
parseAndTypeCheck inputString =
  case Parser.parseText Parser.term (toS inputString) "<command-line>" of
    Parsix.Success preTerm -> do
      context <- Context.empty
      Elaboration.Inferred term typeValue <- Elaboration.infer context preTerm
      print term
      typeValue' <- force typeValue
      type_ <- Readback.readback (Context.toReadbackEnvironment context) typeValue'
      print type_
    Parsix.Failure err -> do
      putText "Parse error"
      print $ Parsix.prettyError err
