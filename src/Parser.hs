{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Parser where

import Prelude (String)
import Protolude hiding (try)

import Data.Char
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.String
import qualified Text.Parser.Token.Highlight as Highlight
import Text.Parsix ((<?>), symbol, try)
import qualified Text.Parsix as Parsix

import PreSyntax

newtype Parser a = Parser (Parsix.Parser a)
  deriving
    ( Monad, MonadPlus, Functor, Applicative, Alternative
    , Parsix.Parsing, Parsix.CharParsing, Parsix.SliceParsing
    )

parseTest :: (MonadIO m, Show a) => Parser a -> String -> m ()
parseTest p s = liftIO $ print $ parseText p (fromString s) "<interactive>"

parseText :: Parser a -> Text -> FilePath -> Parsix.Result a
parseText (Parser p) =
  Parsix.parseText (p <* Parsix.eof)

-------------------------------------------------------------------------------
-- Tokenisation

idStart, idLetter :: Parser Char
idStart = Parsix.satisfy isAlpha <|> Parsix.oneOf "_"
idLetter = Parsix.satisfy isAlphaNum <|> Parsix.oneOf "_'"

reservedIds :: HashSet String
reservedIds = HashSet.fromList ["let", "in"]

idStyle :: Parsix.IdentifierStyle Parser
idStyle = Parsix.IdentifierStyle "identifier" idStart idLetter reservedIds Highlight.Identifier Highlight.ReservedIdentifier

instance Parsix.TokenParsing Parser where
  someSpace =
    Parsix.skipSome (Parsix.satisfy isSpace) *> (comments <|> pure ())
    <|> comments
    where
      comments =
        Parsix.highlight
          Highlight.Comment
          (lineComment <|> multilineComment)
        *> Parsix.whiteSpace
  highlight h (Parser p) = Parser $ Parsix.highlight h p

lineComment :: Parser ()
lineComment =
  () <$ Parsix.string "--"
    <* Parsix.manyTill Parsix.anyChar (Parsix.char '\n')
    <?> "line comment"

multilineComment :: Parser ()
multilineComment =
  () <$ Parsix.string "{-" <* inner
  <?> "multi-line comment"
  where
    inner =
      Parsix.string "-}"
      <|> multilineComment *> inner
      <|> Parsix.anyChar *> inner

reserved :: Text -> Parser ()
reserved = Parsix.reserveText idStyle

var :: Parser Var
var = Parsix.ident idStyle

-------------------------------------------------------------------------------
-- Terms

atomicTerm :: Parser Term
atomicTerm =
  symbol "(" *> term <* symbol ")"
  <|> Var <$> var
  <|> Let <$ reserved "let" <*> var <* symbol "=" <*> term <* reserved "in" <*> term
  <|> Lam <$ symbol "\\" <*> var <* symbol "." <*> term
  <?> "term"

term :: Parser Term
term =
  Pi <$> try (symbol "(" *> var <* reserved ":") <*> term <* symbol ")" <* symbol "->" <*> term
  <|> apps <$> atomicTerm <*> many atomicTerm <**> fun
  <?> "term"
  where
    fun =
      flip Fun <$ symbol "->" <*> term
      <|> pure identity
