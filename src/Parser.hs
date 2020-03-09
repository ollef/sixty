{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
module Parser where

import Protolude hiding (break, try, moduleName)

import Control.Monad.Fail
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Text.Parser.Combinators (sepBy, sepBy1)

import Boxity
import qualified Error.Parsing as Error
import qualified Lexer
import Lexer (Token(Token), UnspannedToken)
import qualified Literal
import qualified Module
import Name (Name(Name))
import qualified Name
import Plicity
import qualified Position
import Presyntax hiding (clause)
import qualified Presyntax
import qualified Span

parseTokens :: Parser a -> [Token] -> Either Error.Parsing a
parseTokens p tokens =
  unParser
    p
    (\a _ -> Right a)
    (\a _ _ -> Right a)
    (\err -> mkError err tokens)
    (\err tokens' -> mkError err tokens')
    tokens
    (Position.LineColumn 0 0)
    (Position.Absolute 0)
  where
    mkError err tokens' =
      Left Error.Parsing
        { Error.reason = _reason err
        , Error.expected = toList $ _expected err
        , Error.position =
          case tokens' of
            [] ->
              Left Error.EOF

            Token _ (Span.Absolute pos _) _:_ ->
              Right pos
        }

-------------------------------------------------------------------------------

data ErrorReason = ErrorReason
  { _reason :: Maybe Text
  , _expected :: HashSet Text
  } deriving Show

instance Semigroup ErrorReason where
  ErrorReason r1 e1 <> ErrorReason r2 e2 =
    ErrorReason (r1 <|> r2) (e1 <> e2)

instance Monoid ErrorReason where
  mempty =
    ErrorReason empty mempty

failed :: Text -> ErrorReason
failed reason =
  ErrorReason (Just reason) mempty

expected :: Text -> ErrorReason
expected s =
  ErrorReason Nothing $ HashSet.singleton s

-------------------------------------------------------------------------------

data Parser a = Parser
  { unParser
    :: forall r
    . (a -> ErrorReason -> r) -- success epsilon
    -> (a -> ErrorReason -> [Token] -> r) -- success committed
    -> (ErrorReason -> r) -- error epsilon
    -> (ErrorReason -> [Token] -> r) -- error committed
    -> [Token] -- input
    -> Position.LineColumn -- indentation base
    -> Position.Absolute -- base position
    -> r
  }

instance Semigroup a => Semigroup (Parser a) where
  (<>) = liftA2 (<>)

instance Monoid a => Monoid (Parser a) where
  mempty = pure mempty

instance Functor Parser where
  fmap f (Parser p) =
    Parser $ \s0 s -> p (s0 . f) (s . f)

instance Applicative Parser where
  pure a = Parser $ \s0 _s _e0 _e _inp _lineCol _base -> s0 a mempty
  (<*>) = ap

instance Alternative Parser where
  empty = Parser $ \_s0 _s e0 _e _inp _lineCol _base -> e0 mempty
  Parser p <|> Parser q =
    Parser $ \s0 s e0 e inp lineCol base ->
      p
        s0
        s
        (\err -> q s0 s (\err' -> e0 $ err <> err') e inp lineCol base)
        e
        inp
        lineCol
        base
  many p = reverse <$> manyAccum (:) p
  some p = (:) <$> p <*> many p

instance Monad Parser where
  return = pure
  Parser p >>= f =
    Parser $ \s0 s e0 e inp lineCol base ->
      p
        (\a err -> unParser (f a)
          (\b err' -> s0 b $ err <> err')
          s
          (\err' -> e0 $ err <> err')
          e
          inp
          lineCol
          base)
        (\a err inp' -> unParser (f a)
          (\b err' -> s b (err <> err') inp')
          s
          (\err' -> e (err <> err') inp')
          e
          inp'
          lineCol
          base)
        e0
        e
        inp
        lineCol
        base

instance MonadFail Parser where
  fail x =
    Parser $ \_s0 _s e0 _e _inp _lineCol _base -> e0 $ failed $ toS x

instance MonadPlus Parser where
  mzero = empty
  mplus = (<|>)

eof :: Parser ()
eof =
  Parser $ \s0 _ e0 _ inp _ _ ->
    case inp of
      [] ->
        s0 () mempty

      _:_ ->
        e0 $ expected "EOF"

manyAccum :: (a -> [a] -> [a]) -> Parser a -> Parser [a]
manyAccum f (Parser p) =
  Parser $ \s0 s _e0 e inp lineCol base -> do
    let manyFailed inp' _ _ =
          e (failed "'many' applied to a parser that accepts an empty string") inp'
        walk xs x err inp' =
          p
            (manyFailed inp')
            (walk $ f x xs)
            (\err' -> s (f x xs) (err <> err') inp')
            e
            inp'
            lineCol
            base
    p (manyFailed inp) (walk []) (s0 []) e inp lineCol base

try :: Parser a -> Parser a
try (Parser p) =
  Parser $ \s0 s e0 _e -> p s0 s e0 (\_err _inp -> e0 mempty)

(<?>) :: Parser a -> Text -> Parser a
Parser p <?> expect =
  Parser $ \s0 s e0 e ->
    p
      (\a -> s0 a . setExpected)
      s
      (e0 . setExpected)
      e
  where
    setExpected e = e { _expected = HashSet.singleton expect }

notFollowedBy :: Parser Text -> Parser ()
notFollowedBy (Parser p) =
  Parser $ \s0 _ e0 _ ->
    p
      (\a _ -> e0 $ failed $ "Unexpected '" <> a <> "'")
      (\a _ _ -> e0 $ failed $ "Unexpected '" <> a <> "'")
      (\_ -> s0 () mempty)
      (\_ _ -> s0 () mempty)

notFollowedByToken :: UnspannedToken -> Parser ()
notFollowedByToken token_ =
  notFollowedBy $ Lexer.displayToken token_ <$ token token_

withRecovery :: (ErrorReason -> Position.Absolute -> [Token] -> Parser a) -> Parser a -> Parser a
withRecovery recover_ (Parser p) = Parser
  $ \s0 s e0 e inp lineCol base ->
    p
      s0
      s
      (\err -> unParser (recover_ err base inp)
        (\a _err' -> s0 a err)
        s
        (\_err' -> e0 err)
        (\_err' _inp' -> e0 err)
        inp
        lineCol
        base)
      (\err inp' -> unParser (recover_ err base inp')
        (\a _err' -> s a err inp)
        s
        (\_err' -> e err inp')
        (\_err' _inp'' -> e err inp')
        inp
        lineCol
        base)
      inp
      lineCol
      base

withToken
  ::
    (forall r
    . (a -> r)
    -> (ErrorReason -> r)
    -> Span.Relative
    -> UnspannedToken
    -> r
    )
  -> Parser a
withToken f =
  Parser $ \_s0 s e0 _e inp _lineCol base ->
    case inp of
      [] ->
        e0 $ failed "Unexpected EOF"

      Token _pos tokenSpan token_:inp' ->
        f
          (\a -> s a mempty inp')
          e0
          (Span.relativeTo base tokenSpan)
          token_

withIndentedToken
  ::
    (forall r
    . (a -> r)
    -> (ErrorReason -> r)
    -> Span.Relative
    -> UnspannedToken
    -> r
    )
  -> Parser a
withIndentedToken f =
  Parser $ \_s0 s e0 _e inp (Position.LineColumn line col) base ->
    case inp of
      [] ->
        e0 $ failed "Unexpected EOF"

      Token (Position.LineColumn tokenLine tokenCol) tokenSpan token_:inp'
        | line == tokenLine || col < tokenCol ->
          f
            (\a -> s a mempty inp')
            e0
            (Span.relativeTo base tokenSpan)
            token_

        | otherwise ->
          e0 $ failed "Unexpected unindent"

withIndentedTokenM
  ::
    (forall r
    . (Parser a -> r)
    -> r
    -> Span.Relative
    -> UnspannedToken
    -> r
    )
  -> Parser a
withIndentedTokenM f =
  Parser $ \_s0 s e0 e inp lineCol@(Position.LineColumn line col) base ->
    case inp of
      [] ->
        e0 $ failed "Unexpected EOF"

      Token (Position.LineColumn tokenLine tokenCol) tokenSpan token_:inp'
        | line == tokenLine || col < tokenCol ->
          f
            (\p ->
              unParser
                p
                (\a err -> s a err inp')
                s
                (\err -> e err inp')
                e
                inp'
                lineCol
                base
            )
            (e0 mempty)
            (Span.relativeTo base tokenSpan)
            token_

        | otherwise ->
          e0 $ failed "Unexpected unindent"

withIndentationBlock :: Parser a -> Parser a
withIndentationBlock p =
  Parser $ \s0 s e0 e inp _lineCol base ->
    case inp of
      [] ->
        e0 $ failed "Unexpected EOF"

      Token tokenLineCol _ _:_ ->
        unParser p s0 s e0 e inp tokenLineCol base

relativeTo :: Parser a -> Parser (Position.Absolute, a)
relativeTo p =
  Parser $ \s0 s e0 e inp lineCol _base ->
    case inp of
      [] ->
        e0 $ failed "Unexpected EOF"

      Token _ (Span.Absolute tokenStart _) _:_ ->
        unParser ((,) tokenStart <$> p) s0 s e0 e inp lineCol tokenStart

sameLevel :: Parser a -> Parser a
sameLevel p =
  Parser $ \s0 s e0 e inp lineCol@(Position.LineColumn _ col) base ->
    case inp of
      [] ->
        e0 $ failed "Unexpected EOF"

      Token (Position.LineColumn _ tokenCol) _ _:_
        | col == tokenCol ->
          unParser p s0 s e0 e inp lineCol base

        | col > tokenCol ->
          e0 $ failed "Unexpected unindent"

        | otherwise ->
          e0 $ failed "Unexpected indent"

indented :: Parser a -> Parser a
indented p =
  Parser $ \s0 s e0 e inp lineCol@(Position.LineColumn line col) base ->
    case inp of
      [] ->
        e0 $ failed "Unexpected EOF"

      Token (Position.LineColumn tokenLine tokenCol) _ _:_
        | line == tokenLine || col < tokenCol ->
          unParser p s0 s e0 e inp lineCol base

        | otherwise ->
          e0 $ failed "Unexpected unindent"

-- | One or more at the same indentation level.
someSame :: Parser a -> Parser [a]
someSame p =
  some (sameLevel $ withIndentationBlock p)

-- | Zero or more at the same indentation level.
manySame :: Parser a -> Parser [a]
manySame p =
  many (sameLevel $ withIndentationBlock p)

blockOfMany :: Parser a -> Parser [a]
blockOfMany p =
  indented (withIndentationBlock $ someSame p)
  <|> pure []

token :: UnspannedToken -> Parser Span.Relative
token t =
  withIndentedToken $ \continue break span t' ->
    if t == t' then
      continue span

    else
      break $ expected $ "'" <> Lexer.displayToken t <> "'"

uncheckedToken :: UnspannedToken -> Parser Span.Relative
uncheckedToken t =
  withToken $ \continue break span t' ->
    if t == t' then
      continue span

    else
      break $ expected $ "'" <> Lexer.displayToken t <> "'"

spannedIdentifier :: Parser (Span.Relative, Text)
spannedIdentifier =
  withIndentedToken $ \continue break span token_ ->
    case token_ of
      Lexer.Identifier name_ ->
        continue (span, name_)

      _ ->
        break $ expected "identifier"

spannedPrename :: Parser (Span.Relative, Name.Pre)
spannedPrename =
  second Name.Pre <$> spannedIdentifier

spannedModuleName :: Parser (Span.Relative, Name.Module)
spannedModuleName =
  second Name.Module <$> spannedIdentifier

spannedName :: Parser (Span.Relative, Name)
spannedName =
  second Name <$> spannedIdentifier

spannedConstructor :: Parser (Span.Relative, Name.Constructor)
spannedConstructor =
  second Name.Constructor <$> spannedIdentifier

binding :: Parser Binding
binding =
  uncurry Binding <$> spannedName

-------------------------------------------------------------------------------
-- Error recovery

recover :: (Error.Parsing -> a) -> ErrorReason -> Position.Absolute -> [Token] -> Parser a
recover k errorReason _base inp = do
  skipToBaseLevel
  pure $
    k $
    Error.Parsing
      (_reason errorReason)
      (HashSet.toList $ _expected errorReason)
      pos
  where
    pos =
      case inp of
        Token _ (Span.Absolute startPos _) _:_ ->
          Right startPos

        _ ->
          Left Error.EOF

skipToBaseLevel :: Parser ()
skipToBaseLevel =
  Parser $ \_s0 s e0 _e inp lineCol _base ->
    case inp of
      _:inp' ->
        s () mempty $ dropWhile (\(Token tokenLineCol _ _) -> lineCol < tokenLineCol) inp'

      _ ->
        e0 $ failed "Unexpected EOF"

-------------------------------------------------------------------------------
-- Patterns

atomicPattern :: Parser Pattern
atomicPattern =
  (<?> "pattern") $
    withIndentedTokenM $ \continue break span token_ ->
      case token_ of
        Lexer.LeftParen ->
          continue $ pattern_ <* token Lexer.RightParen

        Lexer.QuestionMark ->
          continue $ pure $ Pattern span $ ConOrVar span "?" mempty

        Lexer.Underscore ->
          continue $ pure $ Pattern span $ WildcardPattern

        Lexer.Forced ->
          continue $ (\term_@(Term termSpan _) -> Pattern termSpan $ Forced term_) <$> atomicTerm

        Lexer.Identifier name_ ->
          continue $ pure $ Pattern span $ ConOrVar span (Name.Pre name_) mempty

        Lexer.Number int ->
          continue $ pure $ Pattern span $ LitPattern $ Literal.Integer int

        _ ->
          break

pattern_ :: Parser Pattern
pattern_ =
  ( uncurry conOrVar <$> spannedPrename <*> many plicitPattern
    <|> atomicPattern
  )
  <**>
  ( flip anno <$ token Lexer.Colon <*> term
    <|> pure identity
  ) <?> "pattern"

plicitPattern :: Parser PlicitPattern
plicitPattern =
  mkImplicitPattern <$>
    token Lexer.LeftImplicitBrace <*>
    sepBy patName (token $ Lexer.Operator ",") <*>
    token Lexer.RightImplicitBrace
  <|> ExplicitPattern <$> atomicPattern
  <?> "explicit or implicit pattern"
  where
    mkImplicitPattern span1 pats span2 =
      ImplicitPattern (Span.add span1 span2) $ HashMap.fromList pats
    patName =
      spannedName <**>
        ((\pat (_, name_) -> (name_, pat)) <$ token Lexer.Equals <*> pattern_
        <|> pure (\(span, name_@(Name n)) -> (name_, Pattern span $ ConOrVar span (Name.Pre n) mempty))
        )

-------------------------------------------------------------------------------
-- Terms

recoveringTerm :: Parser Term
recoveringTerm =
  withRecovery
    (\errorInfo base inp' -> 
      case inp' of
        Token _ tokenSpan _:_ ->
          recover (Term (Span.relativeTo base tokenSpan) . ParseError) errorInfo base inp'

        _ ->
          empty
    )
    term

atomicTerm :: Parser Term
atomicTerm =
  (<?> "term") $
    withIndentedTokenM $ \continue break span token_ ->
      case token_ of
        Lexer.LeftParen ->
          continue $ term <* token Lexer.RightParen

        Lexer.Let ->
          continue $
            flip (foldr ($)) <$> blockOfMany letBinding <* token Lexer.In <*> term

        Lexer.Underscore ->
          continue $ pure $ Term span Wildcard

        Lexer.QuestionMark ->
          continue $ pure $ Term span Wildcard

        Lexer.Identifier ident ->
          continue $ pure $ Term span $ Var $ Name.Pre ident

        Lexer.Case ->
          continue $
            case_ span <$> term <*> token Lexer.Of <*> blockOfMany branch

        Lexer.Lambda ->
          continue $
            lams <$> some plicitPattern <* token Lexer.Dot <*> term

        Lexer.Forall ->
          continue $
            implicitPis <$>
              some
                ( (,) <$ token Lexer.LeftParen <*> some binding <* token Lexer.Colon <*> term <* token Lexer.RightParen
                <|> (\binding_@(Binding span_ _) -> ([binding_], Term span_ Wildcard)) <$> binding
                )
                <* token Lexer.Dot <*> term

        Lexer.Number int ->
          continue $ pure $ Term span $ Lit $ Literal.Integer int

        _ ->
          break
  where
    implicitPis vss target =
      foldr (\(vs, domain) target' -> pis Implicit vs domain target') target vss

    branch :: Parser (Pattern, Term)
    branch =
      (,) <$> pattern_ <* token Lexer.RightArrow <*> term

    letBinding :: Parser (Term -> Term)
    letBinding = do
      Binding span name_@(Name nameText) <- binding
      let_ span name_ . Just . (,) span <$ token Lexer.Colon <*> recoveringTerm <*>
        sameLevel (withIndentationBlock $ do
          span' <- token $ Lexer.Identifier nameText
          clauses span' nameText)
        <|> let_ span name_ Nothing <$> clauses span nameText

plicitAtomicTerm :: Parser (Term -> Term)
plicitAtomicTerm =
  (\args span fun -> implicitApp fun (HashMap.fromList args) span) <$ token Lexer.LeftImplicitBrace <*>
    sepBy implicitArgument (token $ Lexer.Operator ",") <*>
    token Lexer.RightImplicitBrace
  <|> flip app <$> atomicTerm
  where
    implicitArgument =
      spannedName <**>
        ((\t (_, n) -> (n, t)) <$ token Lexer.Equals <*> term
        <|> pure (\(span, n@(Name text)) -> (n, Term span $ Var $ Name.Pre text))
        )

term :: Parser Term
term =
  pis Explicit <$>
    try (token Lexer.LeftParen *> some binding <* token Lexer.Colon) <*>
    term <* token Lexer.RightParen <*
    token Lexer.RightArrow <*> term
  <|> atomicTerm <**> (foldl' (flip (.)) identity <$> many plicitAtomicTerm) <**> fun
  <?> "term"
  where
    fun =
      flip function <$ token Lexer.RightArrow <*> term
      <|> pure identity

-------------------------------------------------------------------------------
-- Definitions

definition :: Parser (Either Error.Parsing (Position.Absolute, (Name, Definition)))
definition =
  withRecovery (recover Left) $
  fmap Right $
  sameLevel $
  withIndentationBlock $
  relativeTo $
    dataDefinition
    <|> do
      (span, name_@(Name nameText)) <- spannedName
      (,) name_ <$>
        (TypeDeclaration span <$ token Lexer.Colon <*> recoveringTerm
        <|> ConstantDefinition <$> clauses span nameText
        )
    <?> "definition"

clauses :: Span.Relative -> Text -> Parser [(Span.Relative, Clause)]
clauses firstSpan nameText =
  (:) <$>
    ((,) firstSpan <$> clause) <*>
    manySame ((,) <$> try (token (Lexer.Identifier nameText) <* notFollowedByToken Lexer.Colon) <*> clause)

clause :: Parser Clause
clause =
  Presyntax.clause <$> many plicitPattern <*> token Lexer.Equals <*> recoveringTerm

dataDefinition :: Parser (Name, Definition)
dataDefinition =
  mkDataDefinition <$> boxity <*> spannedName <*> parameters <*>
    (token Lexer.Where *> blockOfMany gadtConstructors
    <|> token Lexer.Equals *> sepBy1 adtConstructor (token Lexer.Pipe)
    )
  where
    boxity =
      Boxed <$ token (Lexer.Identifier "boxed") <* uncheckedToken Lexer.Data
      <|> Unboxed <$ token Lexer.Data

    mkDataDefinition boxity_ (span, name_) params constrs =
      (name_, DataDefinition span boxity_ params constrs)
    parameters =
      parameters1 <|> pure []

    parameters1 =
      implicitParameters
      <|> (<>) <$> explicitParameter <*> parameters

    explicitParameter =
      (\bindings type_ -> [(binding_, type_, Explicit) | binding_ <- bindings]) <$ token Lexer.LeftParen <*> some binding <* token Lexer.Colon <*> recoveringTerm <* token Lexer.RightParen
      <|> (\binding_@(Binding span _) -> pure (binding_, Term span Presyntax.Wildcard, Explicit)) <$> binding

    implicitParameters =
      (<>) . concat <$ token Lexer.Forall <*>
        some
          ((\bindings type_ -> [(binding_, type_, Implicit) | binding_ <- bindings]) <$ token Lexer.LeftParen <*> some binding <* token Lexer.Colon <*> term <* token Lexer.RightParen
          <|> (\binding_@(Binding span _) -> [(binding_, Term span Wildcard, Implicit)]) <$> binding
          ) <* token Lexer.Dot <*> parameters1

    gadtConstructors =
      withIndentationBlock $
        GADTConstructors <$> some spannedConstructor <* token Lexer.Colon <*> recoveringTerm

    adtConstructor =
      uncurry ADTConstructor <$> spannedConstructor <*> many atomicTerm

-------------------------------------------------------------------------------
-- Module

module_ :: Parser ((Maybe (Span.Absolute, Name.Module), Module.Header), [Either Error.Parsing (Position.Absolute, (Name, Definition))])
module_ =
  (,) <$> moduleHeader <*> many definition

moduleHeader :: Parser (Maybe (Span.Absolute, Name.Module), Module.Header)
moduleHeader =
  mkModuleHeader <$> moduleExposing <*> manySame import_
  where
    mkModuleHeader (mname, exposed) imports =
      (mname, Module.Header exposed imports)
    moduleExposing =
      sameLevel $ withIndentationBlock ((\(span, name) exposed -> (Just (Span.absoluteFrom 0 span, name), exposed)) <$ token (Lexer.Identifier "module") <*> spannedModuleName <* token (Lexer.Identifier "exposing") <*> exposedNames)
      <|> pure (Nothing, Module.AllExposed)

import_ :: Parser Module.Import
import_ =
  sameLevel $
  withIndentationBlock $
    mkImport
      <$ token (Lexer.Identifier "import") <*> spannedModuleName
      <*>
        (Just <$ token (Lexer.Identifier "as") <*> spannedPrename
        <|> pure Nothing
        )
      <*>
        (Just <$ token (Lexer.Identifier "exposing") <*> exposedNames
        <|> pure Nothing
        )
  where
    mkImport (span, n@(Name.Module text)) malias mexposed =
      Module.Import
        { _span = absoluteSpan
        , _module = n
        , _alias = maybe (absoluteSpan, Name.Pre text) (first $ Span.absoluteFrom 0) malias
        , _importedNames = fold mexposed
        }
      where
        absoluteSpan =
          Span.absoluteFrom 0 span

exposedNames :: Parser Module.ExposedNames
exposedNames =
  token Lexer.LeftParen *> inner <* token Lexer.RightParen
  where
    inner =
      Module.AllExposed <$ token (Lexer.Operator "..")
      <|> Module.Exposed . HashSet.fromList <$> sepBy (snd <$> spannedPrename) (token $ Lexer.Operator ",")
