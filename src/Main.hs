{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Protolude hiding (force)

import qualified Data.HashMap.Lazy as HashMap
import Data.IORef
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import qualified Text.Parsix as Parsix

import qualified Context
import qualified Elaboration
import qualified Meta
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
    Parsix.Success preTerm ->
      runM $ do
        context <- Context.empty
        Elaboration.Inferred term typeValue <- Elaboration.infer context preTerm
        putText "Term:"
        liftIO $ putDoc $ Pretty.prettyTerm 0 Pretty.empty term <> line
        typeValue' <- force typeValue
        type_ <- Readback.readback (Context.toReadbackEnvironment context) typeValue'
        putText "Type:"
        liftIO $ putDoc $ Pretty.prettyTerm 0 Pretty.empty type_ <> line
        putText "Metas:"
        metas <- liftIO $ readIORef (Context.metas context)
        liftIO $ forM_ (HashMap.toList $ Meta.vars metas) $ \(Meta.Index i, metaSolution) ->
          case metaSolution of
            Meta.Unsolved metaType ->
              putDoc
                $ "?" <> pretty i
                <> " : "
                <> Pretty.prettyTerm 0 Pretty.empty metaType <> line

            Meta.Solved solution ->
              putDoc
                $ "?" <> pretty i
                <> " = "
                <> Pretty.prettyTerm 0 Pretty.empty solution <> line

    Parsix.Failure err -> do
      putText "Parse error"
      print $ Parsix.prettyError err
