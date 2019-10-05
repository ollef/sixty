{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import Protolude hiding (check, force)

import qualified Data.Text as Text
import Options.Applicative

import qualified Command.Check as Command
import qualified Command.Watch as Command
import qualified LanguageServer

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
  <> command "watch" watchCommand
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
      (Command.check <$>
        many (strArgument
        $ metavar "FILES..."
        <> help
          (toS $ Text.unlines
            [ "Input source files, project files, or directories."
            , "If no files are given, I will look for a 'sixten.json' file in the current directory and its parent directories."
            ]
          )
        <> action "file"
        )
      )
    )
    $ fullDesc
    <> progDesc "Type check a Sixten program"
    <> header "sixten check"

watchCommand :: ParserInfo (IO ())
watchCommand =
  info
    (helper <*>
      (Command.watch <$>
        many (strArgument
        $ metavar "FILES..."
        <> help
          (toS $ Text.unlines
            [ "Input source files, project files, or directories."
            , "If no files are given, I will look for a 'sixten.json' file in the current directory and its parent directories."
            ]
          )
        <> action "file"
        )
      )
    )
    $ fullDesc
    <> progDesc "Type check a Sixten program, watching for changes"
    <> header "sixten watch"
