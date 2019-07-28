{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
{-# language TupleSections #-}
module Parser where

import Prelude (String)
import Protolude hiding (try)

import Data.Char
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Set as Set
import Data.String
import qualified Text.Parser.LookAhead as LookAhead
import qualified Text.Parser.Token.Highlight as Highlight
import Text.Parsix ((<?>), symbol, try)
import qualified Text.Parsix as Parsix

import qualified Error
import Name (Name(Name))
import qualified Name
import Plicity
import qualified Position
import Presyntax
import qualified Span

data Environment = Environment
  { indentationBlockStart :: !Parsix.Position
  , basePosition :: !Position.Absolute
  }

newtype Parser a = Parser { unparser :: ReaderT Environment Parsix.Parser a }
  deriving
    ( Monad, MonadReader Environment, MonadPlus, Functor, Applicative, Alternative
    , Parsix.Parsing, Parsix.CharParsing, Parsix.SliceParsing, LookAhead.LookAheadParsing
    , Parsix.RecoveryParsing
    )

parseTest :: (MonadIO m, Show a) => Parser a -> String -> m ()
parseTest p s =
  liftIO $ print $ parseText p (fromString s) "<interactive>"

parseText :: Parser a -> Text -> FilePath -> Either Error.Parsing a
parseText p input filePath =
  case Parsix.parseText (runReaderT (unparser $ Parsix.whiteSpace *> p <* Parsix.eof) startEnv) input filePath of
    Parsix.Success a ->
      Right a

    Parsix.Failure err ->
      Left $
        Error.Parsing
          { Error.reason = Parsix.errorReason err
          , Error.expected = toList $ Parsix.errorExpected err
          , Error.position = Position.Absolute $ Parsix.codeUnits $ Parsix.errorPosition err
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
  <|> pure []

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
-- Error recovery

recover :: (Error.Parsing -> a) -> Parsix.ErrorInfo -> Parsix.Position -> Parser a
recover k errorInfo pos = do
  skipToBaseLevel
  pure $
    k $
    Error.Parsing
      (Parsix.errorInfoReason errorInfo)
      (Set.toList $ Parsix.errorInfoExpected errorInfo)
      (Position.Absolute (Parsix.codeUnits pos))

skipToBaseLevel :: Parser ()
skipToBaseLevel =
  Parsix.token $ Parsix.anyChar >> Parsix.skipMany (indented Parsix.anyChar)

-------------------------------------------------------------------------------
-- Positions

position :: Parser Position.Absolute
position =
  Position.Absolute . Parsix.codeUnits <$> Parsix.position

relativeTo :: Parser a -> Parser (Position.Absolute, a)
relativeTo parser = do
  p <- position
  result <- local (\env -> env { basePosition = p }) parser
  pure (p, result)

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
  Parsix.satisfy isIdStart
    where
      isIdStart c =
        isAlpha c || c == '_'
idLetter =
  Parsix.satisfy isIdLetter
    where
      isIdLetter c =
        isAlphaNum c || c == '_' || c == '\''
qidLetter = idLetter
  <|> Parsix.try (Parsix.char '.' <* LookAhead.lookAhead idLetter)

reservedIds :: HashSet String
reservedIds =
  HashSet.fromList ["let", "in", "_", "data", "where", "forall", "case", "of"]

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

constructor :: Parser Name.Constructor
constructor =
  Parsix.ident idStyle

prename :: Parser Name.Pre
prename =
  Parsix.ident qidStyle

-------------------------------------------------------------------------------
-- Patterns

spannedPattern :: Parser UnspannedPattern -> Parser Pattern
spannedPattern =
  fmap (uncurry Pattern) . spanned

atomicPattern :: Parser Pattern
atomicPattern =
  symbol "(" *>% pattern <*% symbol ")"
  <|> spannedPattern
    ((`ConOrVar` mempty) <$> prename
    <|> WildcardPattern <$ reserved "_"
    <|> Forced <$ symbol "~" <*>% atomicTerm
    )
  <?> "pattern"

pattern :: Parser Pattern
pattern =
  ( spannedPattern (ConOrVar <$> prename <*> manyIndented plicitPattern)
    <|> atomicPattern
  )
  <**>
  ( flip anno <$% symbol ":" <*> term
    <|> pure identity
  ) <?> "pattern"

plicitPattern :: Parser PlicitPattern
plicitPattern =
  uncurry ImplicitPattern <$> spanned (HashMap.fromList <$ symbol "@{" <*> sepByIndented patName (symbol ",") <*% symbol "}")
  <|> ExplicitPattern <$> atomicPattern
  <?> "explicit or implicit pattern"
  where
    patName =
      spanned name <**>
        ((\pat (_, name_) -> (name_, pat)) <$% symbol "=" <*>% pattern
        <|> pure (\(span, name_@(Name n)) -> (name_, Pattern span $ ConOrVar (Name.Pre n) mempty))
        )

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
      <|> Case <$ reserved "case" <*>% term <*% reserved "of" <*> blockOfMany branch
      <|> unspanned <$>
        ( lams <$ symbol "\\" <*> someIndented lamName <*% symbol "." <*>% term
        <|> implicitPis <$ reserved "forall" <*>
          someIndented
            ( (,) <$ symbol "(" <*> someIndented (positioned name) <*% symbol ":" <*>% term <*% symbol ")"
            <|> (\(span@(Span.Relative pos _), name_) -> ([(pos, name_)], Term span Wildcard)) <$> spanned name
            ) <*% symbol "." <*>% term
        )
    )
  <?> "term"
  where
    implicitPis vss domain =
      foldr (\(vs, source) domain' -> pis Implicit vs source domain') domain vss

    lamName =
      positioned $
        Right <$> name <|> Left <$> implicitNames

    implicitNames =
      HashMap.fromList <$ symbol "@{" <*>% sepByIndented implicitName (symbol ",") <*% symbol "}"

    implicitName =
      name <**>
        ((\n' n -> (n, n')) <$% symbol "=" <*>% name
        <|> pure (\n -> (n, n))
        )

    branch :: Parser (Pattern, Term)
    branch =
      (,) <$> pattern <*% symbol "->" <*>% term

plicitAtomicTerm :: Parser (Either (HashMap Name Term) Term)
plicitAtomicTerm =
  Left . HashMap.fromList <$ symbol "@{" <*>%
    sepByIndented implicitArgument  (symbol ",") <*%
    symbol "}"
  <|> Right <$> atomicTerm
  where
    implicitArgument =
      spanned name <**>
        ((\t (_, n) -> (n, t)) <$% symbol "=" <*>% term
        <|> pure (\(span, n@(Name text)) -> (n, Term span $ Var $ Name.Pre text))
        )

term :: Parser Term
term =
  spannedTerm (unspanned <$> (pis Explicit <$> try (symbol "(" *> someIndented (positioned name) <*% symbol ":") <*>% term <*% symbol ")" <*% symbol "->" <*>% term))
  <|> apps <$> atomicTerm <*> manyIndented (spanned plicitAtomicTerm) <**> fun
  <?> "term"
  where
    fun =
      flip function <$% symbol "->" <*>% term
      <|> pure identity

-------------------------------------------------------------------------------
-- Definitions

module_ :: Parser [Either Error.Parsing (Position.Absolute, (Name, Definition))]
module_ =
  many definition

definition :: Parser (Either Error.Parsing (Position.Absolute, (Name, Definition)))
definition =
  Parsix.withRecovery (recover Left) $
  fmap Right $
  sameLevel $
  withIndentationBlock $
  relativeTo $
    (,) <$ reserved "data" <*>% name <*>
      (DataDefinition <$> manyIndented param <*% reserved "where" <*> blockOfMany constr)
    <|> do
      name_@(Name nameText) <- name
      (,) name_ <$>%
        (TypeDeclaration <$ symbol ":" <*>% recoveringTerm
        <|> ConstantDefinition <$> clauses nameText
        )
    <?> "definition"
  where
    recoveringTerm =
      Parsix.withRecovery
        (\errorInfo -> spannedTerm . recover ParseError errorInfo)
        (indented term)
    param =
      -- TODO support implicit parameters
      (,, Explicit) <$ symbol "(" <*>% name <*% symbol ":" <*>% recoveringTerm <*% symbol ")"
      <|> (\(span, name_) -> (name_, Term span Presyntax.Wildcard, Explicit)) <$> spanned name
    constr =
      (,) <$> constructor <*% symbol ":" <*>% recoveringTerm
    clauses nameText =
      (:) <$>
        clause <*>
        manySame (withIndentationBlock $ reserved nameText *> clause)
      where
        clause =
          (\(span, (pats, rhs)) -> Clause span pats rhs) <$>
          spanned ((,) <$> manyIndented plicitPattern <*% symbol "=" <*>% recoveringTerm)
