{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Protolude hiding (force)

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import qualified Text.Parsix as Parsix

import qualified Context
import qualified Elaboration
import Monad
import qualified Parser
import qualified Pretty
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
      putDoc $ Pretty.prettyTerm 0 Pretty.empty term <> line
      typeValue' <- force typeValue
      type_ <- Readback.readback (Context.toReadbackEnvironment context) typeValue'
      putDoc $ Pretty.prettyTerm 0 Pretty.empty type_ <> line
    Parsix.Failure err -> do
      putText "Parse error"
      print $ Parsix.prettyError err
