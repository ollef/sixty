{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import Protolude hiding (check, force)

import qualified Data.HashSet as HashSet
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Options.Applicative
import Rock

import qualified Driver
import qualified LanguageServer
import qualified Name
import qualified Pretty
import qualified Query
import qualified Syntax

main :: IO ()
main =
  join $ execParser optionsParser

optionsParser :: ParserInfo (IO ())
optionsParser =
  info (helper <*> commands)
    $ fullDesc
    <> progDesc "Sixten compiler"
    <> header "sixten"

commands :: Parser (IO ())
commands = subparser
  $ command "check" checkCommand
  <> command "language-server" languageServerCommand

languageServerCommand :: ParserInfo (IO ())
languageServerCommand =
  info (pure LanguageServer.run)
    $ fullDesc
    <> progDesc "Start a language server"
    <> header "sixten language-server"

checkCommand :: ParserInfo (IO ())
checkCommand =
  info
    (helper <*>
      (check <$>
        many (strArgument
        $ metavar "FILES..."
        <> help "Input source FILES or directories"
        <> action "file"
        )
      )
    )
    $ fullDesc
    <> progDesc "Type check a Sixten program"
    <> header "sixten check"

check :: [FilePath] -> IO ()
check filePaths = do
  ((), errs) <- Driver.runTask filePaths $
    forM_ filePaths $ \filePath -> do
      (module_, _, defs) <- fetch $ Query.ParsedFile filePath
      let
        names =
          HashSet.fromList $
            Name.Qualified module_ . fst . snd <$> defs
      emptyPrettyEnv <- Pretty.emptyM module_
      liftIO $ putDoc $ "module" <+> pretty module_ <> line <> line
      forM_ names $ \name -> do
        type_ <- fetch $ Query.ElaboratedType name
        liftIO $ putDoc $ Pretty.prettyDefinition emptyPrettyEnv name (Syntax.TypeDeclaration type_) <> line
        maybeDef <- fetch $ Query.ElaboratedDefinition name
        liftIO $ do
          forM_ maybeDef $ \(def, _) ->
            putDoc $ Pretty.prettyDefinition emptyPrettyEnv name def <> line
          putDoc line
  forM_ errs $ \err ->
    liftIO $ putDoc $ pretty err <> line
