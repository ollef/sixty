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

data Environment = Environment
  { indentationBlockStart :: !Parsix.Position
  , basePosition :: !Position.Absolute
  }

newtype Parser a = Parser (ReaderT Environment Parsix.Parser a)
  deriving
    ( Monad, MonadReader Environment, MonadPlus, Functor, Applicative, Alternative
    , Parsix.Parsing, Parsix.CharParsing, Parsix.SliceParsing, LookAhead.LookAheadParsing
    )

parseTest :: (MonadIO m, Show a) => Parser a -> String -> m ()
parseTest p s =
  liftIO $ print $ parseText p (fromString s) "<interactive>"

parseText :: Parser a -> Text -> FilePath -> Either Error.Parsing a
parseText (Parser p) input filePath =
  case Parsix.parseText (Parsix.whiteSpace *> runReaderT p startEnv <* Parsix.eof) input filePath of
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
  where
    startEnv = Environment
      { indentationBlockStart = mempty
      , basePosition = 0
      }

-------------------------------------------------------------------------------
-- Indentation parsing

withIndentationBlock :: Parser a -> Parser a
withIndentationBlock p = do
  pos <- Parsix.position
  local (\env -> env { indentationBlockStart = pos }) p

-- | Check that the current indentation level is the same as the block start
sameLevel :: Parser a -> Parser a
sameLevel p = do
  pos <- Parsix.position
  anchor <- asks indentationBlockStart
  case comparing Parsix.visualColumn pos anchor of
    LT ->
      Parsix.unexpected "unindent"

    EQ ->
      p

    GT ->
      Parsix.unexpected "indent"

-- | Check that the current position is on the same line as the block start or
-- on a successive line but more indented.
indented :: Parser a -> Parser a
indented p = do
  pos <- Parsix.position
  anchor <- asks indentationBlockStart
  case (comparing Parsix.visualRow pos anchor, comparing Parsix.visualColumn pos anchor) of
    (EQ, _) ->
      p -- Same line

    (GT, GT) ->
      p -- Indented

    (_,  _) ->
      Parsix.unexpected "unindent"

-- | One or more at the same indentation level.
someSame :: Parser a -> Parser [a]
someSame p =
  Parsix.some (sameLevel p)

-- | Zero or more at the same indentation level.
manySame :: Parser a -> Parser [a]
manySame p =
  Parsix.many (sameLevel p)

blockOfMany :: Parser a -> Parser [a]
blockOfMany p =
  Parsix.option [] $
  indented $
  withIndentationBlock (someSame p)

optionalIndented :: Parser a -> Parser (Maybe a)
optionalIndented p =
  Parsix.optional (indented p)

-- | One or more on the same line or a successive but indented line.
someIndented :: Parser a -> Parser [a]
someIndented p =
  Parsix.some (indented p)

-- | Zero or more on the same line or a successive but indented line.
manyIndented :: Parser a -> Parser [a]
manyIndented p =
  Parsix.many (indented p)

sepByIndented :: Parser a -> Parser sep -> Parser [a]
sepByIndented p sep =
  (:) <$> p <*> manyIndented (sep *>% p)

-- * Applicative style combinators for checking that the second argument parser
--   is on the same line or indented compared to the anchor.
infixl 4 <$>%, <$%, <*>%, <*%, *>%, <**>%
(<$>%) :: (a -> b) -> Parser a -> Parser b
f <$>% p =
  f <$> indented p

(<$%) :: a -> Parser b -> Parser a
f <$% p =
  f <$ indented p

(<*>%) :: Parser (a -> b) -> Parser a -> Parser b
p <*>% q =
  p <*> indented q

(<*%) :: Parser a -> Parser b -> Parser a
p <*% q =
  p <* indented q

(*>%) :: Parser a -> Parser b -> Parser b
p *>% q =
  p *> indented q

(<**>%) :: Parser a -> Parser (a -> b) -> Parser b
p <**>% q =
  p <**> indented q

-------------------------------------------------------------------------------
-- Positions

position :: Parser Position.Absolute
position =
  Position.Absolute . Parsix.codeUnits <$> Parsix.position

relativeTo :: Parser a -> Parser (Position.Absolute, a)
relativeTo parser = do
  p <- position
  result <- local (\env -> env { basePosition = p }) parser
  return (p, result)

spanned :: Parser a -> Parser (Span.Relative, a)
spanned parser = do
  base <- asks basePosition
  start <- position
  result <- parser
  end <- position
  pure (Span.relativeTo base (Span.Absolute start end), result)

positioned :: Parser a -> Parser (Position.Relative, a)
positioned parser = do
  base <- asks basePosition
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
  symbol "(" *>% term <*% symbol ")"
  <|> spannedTerm
    ( Wildcard <$ reserved "_"
      <|> Var <$> prename
      <|> Let <$ reserved "let" <*>% name <*% symbol "=" <*>% term <*% reserved "in" <*>% term
      <|> unspanned <$> (lams <$ symbol "\\" <*> someIndented (positioned name) <*% symbol "." <*>% term)
    )
  <?> "term"

term :: Parser Term
term =
  spannedTerm (unspanned <$> (pis <$> try (symbol "(" *> someIndented (positioned name) <*% reserved ":") <*>% term <*% symbol ")" <*% symbol "->" <*>% term))
  <|> apps <$> atomicTerm <*> manyIndented atomicTerm <**> fun
  <?> "term"
  where
    fun =
      flip function <$% symbol "->" <*>% term
      <|> pure identity

-------------------------------------------------------------------------------
-- Definitions

module_ :: Parser [(Position.Absolute, Definition)]
module_ =
  blockOfMany definition

definition :: Parser (Position.Absolute, Definition)
definition =
  relativeTo $
  withIndentationBlock $
    name <**>%
      (flip TypeDeclaration <$ symbol ":" <*>% term
      <|> flip ConstantDefinition <$ symbol "=" <*>% term
      )
    <?> "definition"
