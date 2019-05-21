{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Parser where

import Prelude (String)
import Protolude hiding (try)

import Data.Char
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.String
import qualified Text.Parser.LookAhead as LookAhead
import qualified Text.Parser.Token.Highlight as Highlight
import Text.Parsix ((<?>), symbol, try)
import qualified Text.Parsix as Parsix

import Name
import Presyntax hiding (Name)
import qualified Presyntax

newtype Parser a = Parser (Parsix.Parser a)
  deriving
    ( Monad, MonadPlus, Functor, Applicative, Alternative
    , Parsix.Parsing, Parsix.CharParsing, Parsix.SliceParsing, LookAhead.LookAheadParsing
    )

parseTest :: (MonadIO m, Show a) => Parser a -> String -> m ()
parseTest p s =
  liftIO $ print $ parseText p (fromString s) "<interactive>"

parseText :: Parser a -> Text -> FilePath -> Parsix.Result a
parseText (Parser p) =
  Parsix.parseText (p <* Parsix.eof)

-------------------------------------------------------------------------------
-- Tokenisation

idStart, idLetter, qidLetter :: Parser Char
idStart =
  Parsix.satisfy isAlpha <|> Parsix.oneOf "_"
idLetter =
  Parsix.satisfy isAlphaNum <|> Parsix.oneOf "_'"
qidLetter = idLetter
  <|> Parsix.try (Parsix.char '.' <* LookAhead.lookAhead idLetter)

reservedIds :: HashSet String
reservedIds =
  HashSet.fromList ["let", "in", "_"]

idStyle :: Parsix.IdentifierStyle Parser
idStyle
  = Parsix.IdentifierStyle "identifier" idStart idLetter reservedIds Highlight.Identifier Highlight.ReservedIdentifier

qidStyle :: Parsix.IdentifierStyle Parser
qidStyle =
  Parsix.IdentifierStyle "identifier" idStart qidLetter reservedIds Highlight.Identifier Highlight.ReservedIdentifier

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
reserved =
  Parsix.reserveText idStyle

name :: Parser Name
name =
  Parsix.ident idStyle

prename :: Parser Presyntax.Name
prename =
  Parsix.ident qidStyle

-------------------------------------------------------------------------------
-- Terms

atomicTerm :: Parser Term
atomicTerm =
  symbol "(" *> term <* symbol ")"
  <|> Wildcard <$ reserved "_"
  <|> Var <$> prename
  <|> Let <$ reserved "let" <*> name <* symbol "=" <*> term <* reserved "in" <*> term
  <|> lams <$ symbol "\\" <*> some name <* symbol "." <*> term
  <?> "term"
  where
    lams vs body = foldr Lam body vs

term :: Parser Term
term =
  pis <$> try (symbol "(" *> some name <* reserved ":") <*> term <* symbol ")" <* symbol "->" <*> term
  <|> apps <$> atomicTerm <*> many atomicTerm <**> fun
  <?> "term"
  where
    pis vs src dst = foldr (`Pi` src) dst vs
    fun =
      flip Fun <$ symbol "->" <*> term
      <|> pure identity

-------------------------------------------------------------------------------
-- Definitions

module_ :: Parser [Definition]
module_ =
  many definition

definition :: Parser Definition
definition =
  name <**>
    (flip TypeDeclaration <$ symbol ":" <*> term
    <|> flip ConstantDefinition <$ symbol "=" <*> term
    ) <* symbol ";"
  <?> "definition"
