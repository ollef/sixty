{-# language OverloadedStrings #-}
module Main where

import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import qualified Gauge
import qualified Lexer
import qualified Lexer2
import qualified Data.ByteString as ByteString
import qualified Parser
import Protolude
import System.Directory
import System.FilePath

main :: IO ()
main = do
  singlesDirectory <- canonicalizePath "tests/singles"
  multisDirectory <- canonicalizePath "tests/multis"
  singleFiles <- listDirectoryRecursive isSourceFile singlesDirectory
  multiFiles <- listDirectoriesWithFilesMatching isSourceFile multisDirectory
  let
    files =
      -- singleFiles <> concatMap snd multiFiles
      ["lol.vix"]
  Gauge.defaultMain
    [ Gauge.BenchGroup file
      [ -- Gauge.bench "read file" $ Gauge.nfAppIO readFile file
      -- ,
      Gauge.env (ByteString.readFile file) $ Gauge.bench "lex2" . Gauge.nf Lexer2.lexByteString
        ,
      Gauge.env (readFile file) $ Gauge.bench "lex" . Gauge.nf Lexer.lexText
      -- , Gauge.env (Lexer.lexText <$> readFile file) $ Gauge.bench "parse" . Gauge.whnf (Parser.parseTokens Parser.module_)
      -- ,
      -- Gauge.env (readFile file) $ Gauge.bench "parse and lex" . Gauge.whnf (Parser.parseTokens Parser.module_ . Lexer.lexText)
      ]
    | file <- files
    ]
  texts <- mapM readFile files
  putText $ "Lines: " <> show (length $ mconcat $ Text.lines <$> texts)
  where
    isSourceFile =
      (== ".vix") . takeExtension

listDirectoryRecursive :: (FilePath -> Bool) -> FilePath -> IO [FilePath]
listDirectoryRecursive p dir = do
  files <- listDirectory dir
  fmap concat $ forM files $ \file -> do
    let path = dir </> file
    isDir <- doesDirectoryExist path
    if isDir then
      listDirectoryRecursive p path

    else
      pure [path | p path]

listDirectoriesWithFilesMatching
  :: (FilePath -> Bool)
  -> FilePath
  -> IO [(FilePath, [FilePath])]
listDirectoriesWithFilesMatching p dir = do
  files <- listDirectory dir
  let
    paths = (dir </>) <$> files
  if any p paths then do
    recursiveFiles <- listDirectoryRecursive p dir
    pure [(dir, recursiveFiles)]

  else
    fmap concat $ forM paths $ \path -> do
      isDir <- doesDirectoryExist path
      if isDir then
        listDirectoriesWithFilesMatching p path

      else
        pure []
