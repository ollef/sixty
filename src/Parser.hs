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
import qualified Position
import Presyntax hiding (Name)
import qualified Presyntax
import qualified Error
import qualified Span

newtype Parser a = Parser (ReaderT Position.Absolute Parsix.Parser a)
  deriving
    ( Monad, MonadReader Position.Absolute, MonadPlus, Functor, Applicative, Alternative
    , Parsix.Parsing, Parsix.CharParsing, Parsix.SliceParsing, LookAhead.LookAheadParsing
    )

parseTest :: (MonadIO m, Show a) => Parser a -> String -> m ()
parseTest p s =
  liftIO $ print $ parseText p (fromString s) "<interactive>"

parseText :: Parser a -> Text -> FilePath -> Either Error.Parsing a
parseText (Parser p) input filePath =
  case Parsix.parseText (runReaderT p 0 <* Parsix.eof) input filePath of
    Parsix.Success a ->
      Right a

    Parsix.Failure err ->
      Left $
        Error.Parsing
          { Error.reason = Parsix.errorReason err
          , Error.expected = toList $ Parsix.errorExpected err
          , Error.position = Position.Absolute $ Parsix.codeUnits $ Parsix.errorPosition err
          , Error.file = filePath
          }

-------------------------------------------------------------------------------
-- Positions

position :: Parser Position.Absolute
position =
  Position.Absolute . Parsix.codeUnits <$> Parsix.position

relativeTo :: Parser a -> Parser (Position.Absolute, a)
relativeTo parser = do
  p <- position
  result <- local (const p) parser
  return (p, result)

spanned :: Parser a -> Parser (Span.Relative, a)
spanned parser = do
  base <- ask
  start <- position
  result <- parser
  end <- position
  pure (Span.relativeTo base (Span.Absolute start end), result)

positioned :: Parser a -> Parser (Position.Relative, a)
positioned parser = do
  base <- ask
  start <- position
  result <- parser
  pure (Position.relativeTo base start, result)

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

spannedTerm :: Parser UnspannedTerm -> Parser Term
spannedTerm =
  fmap (uncurry Term) . spanned

atomicTerm :: Parser Term
atomicTerm =
  symbol "(" *> term <* symbol ")"
  <|> spannedTerm
    ( Wildcard <$ reserved "_"
      <|> Var <$> prename
      <|> Let <$ reserved "let" <*> name <* symbol "=" <*> term <* reserved "in" <*> term
      <|> unspanned <$> (lams <$ symbol "\\" <*> some (positioned name) <* symbol "." <*> term)
    )
  <?> "term"

term :: Parser Term
term =
  spannedTerm (unspanned <$> (pis <$> try (symbol "(" *> some (positioned name) <* reserved ":") <*> term <* symbol ")" <* symbol "->" <*> term))
  <|> apps <$> atomicTerm <*> many atomicTerm <**> fun
  <?> "term"
  where
    fun =
      flip function <$ symbol "->" <*> term
      <|> pure identity

-------------------------------------------------------------------------------
-- Definitions

module_ :: Parser [(Position.Absolute, Definition)]
module_ =
  many definition

definition :: Parser (Position.Absolute, Definition)
definition =
  relativeTo $
    name <**>
      (flip TypeDeclaration <$ symbol ":" <*> term
      <|> flip ConstantDefinition <$ symbol "=" <*> term
      ) <* symbol ";"
    <?> "definition"
