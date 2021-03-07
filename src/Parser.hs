{-# language DataKinds #-}
{-# language PolyKinds #-}
{-# language BlockArguments #-}
{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language RankNTypes #-}
{-# language UnboxedTuples #-}
module Parser where

import Protolude hiding (break, try, moduleName, Option)

import Control.Monad.Fail
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Text.Parser.Combinators (sepBy, sepBy1)
import GHC.Exts hiding (toList)

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
import qualified Surface.Syntax as Surface
import qualified Span

parseTokens :: Parser a -> [Token] -> Either Error.Parsing a
parseTokens p tokens =
  case unParser p ConsumedNone tokens mempty (Position.LineColumn 0 0) (Position.Absolute 0) of
    OK a _ _ _ ->
      Right a

    Fail _ tokens' err ->
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

newtype Parser a = Parser
  { unParser
    :: Consumed
    -> [Token] -- input
    -> ErrorReason -- previous errors at this position
    -> Position.LineColumn -- indentation base
    -> Position.Absolute -- base position
    -> Result a
  }

data Consumed
  = ConsumedNone
  | ConsumedSome
  deriving (Eq, Ord, Show)

type Option a = (# a | (##) #)

pattern Some :: a -> Option a
pattern Some a = (# a | #)

pattern None :: Option a
pattern None = (# | (##) #)

{-# complete Some, None #-}

type Result a = (# Option a, Consumed, [Token], ErrorReason #)
type ResultRep = 'TupleRep '[ 'SumRep '[ 'LiftedRep, 'TupleRep '[]], 'LiftedRep, 'LiftedRep, 'LiftedRep ]

pattern OK :: a -> Consumed -> [Token] -> ErrorReason -> Result a
pattern OK a con inp err = (# Some a, con, inp, err #)

pattern Fail :: Consumed -> [Token] -> ErrorReason -> Result a
pattern Fail con inp err = (# None, con, inp, err #)

{-# complete OK, Fail #-}

{-# inline mapResult #-}
mapResult :: (a -> b) -> Result a -> Result b
mapResult f (OK a con inp err) = OK (f a) con inp err
mapResult _ (Fail con inp err) = Fail con inp err

instance Functor Parser where
  {-# inline fmap #-}
  fmap f (Parser p) =
    Parser \con inp err lineCol base ->
      mapResult f (p con inp err lineCol base)

instance Applicative Parser where
  {-# inline pure #-}
  pure a =
    Parser \con inp err _ _ -> OK a con inp err

  {-# inline (<*>) #-}
  Parser p <*> Parser q =
    Parser $ \con inp err lineCol base ->
      case p con inp err lineCol base of
        OK f con' inp' err' ->
          mapResult f (q con' inp' err' lineCol base)

        Fail con' inp' err' ->
          Fail con' inp' err'

  {-# inline (*>) #-}
  Parser p *> Parser q =
    Parser $ \con inp err lineCol base ->
      case p con inp err lineCol base of
        OK _ con' inp' err' ->
          q con' inp' err' lineCol base

        Fail con' inp' err' ->
          Fail con' inp' err'

  {-# inline (<*) #-}
  Parser p <* Parser q =
    Parser $ \con inp err lineCol base ->
      case p con inp err lineCol base of
        OK a con' inp' err' ->
          mapResult (const a) (q con' inp' err' lineCol base)

        f ->
          f

instance Alternative Parser where
  {-# inline empty #-}
  empty =
    Parser \con inp err _ _ -> Fail con inp err

  {-# inline (<|>) #-}
  Parser p <|> Parser q =
    Parser \con inp err lineCol base ->
      case p ConsumedNone inp err lineCol base of
        OK a con' inp' err' ->
          OK a (max con con') inp' err'

        Fail ConsumedNone _inp err' ->
          q con inp err' lineCol base

        f@(Fail ConsumedSome _ _) ->
          f

instance Monad Parser where
  {-# inline (>>=) #-}
  Parser p >>= f =
    Parser \con inp err lineCol base ->
      case p con inp err lineCol base of
        OK a con' inp' err' ->
          unParser (f a) con' inp' err' lineCol base

        Fail con' inp' err' ->
          Fail con' inp' err'

  {-# inline (>>) #-}
  (>>) = (*>)

instance MonadFail Parser where
  fail =
    error . failed . toS

instance MonadPlus Parser where
  mzero = empty
  mplus = (<|>)

error :: ErrorReason -> Parser a
error err =
  Parser \con inp err' _ _ -> Fail con inp $ err' <> err

try :: Parser a -> Parser a
try (Parser p) =
  Parser \con inp err lineCol base ->
    case p con inp err lineCol base of
      ok@OK {} ->
        ok

      Fail {} ->
        Fail con inp err

eof :: Parser ()
eof =
  Parser $ \con inp err _ _ ->
    case inp of
      [] ->
        OK () con inp err

      _:_ ->
        Fail con inp $ err <> expected "EOF"

(<?>) :: Parser a -> Text -> Parser a
Parser p <?> expect =
  Parser \con inp err lineCol base ->
    case p con inp err lineCol base of
      (# oa, con', inp', err' #) ->
        (# oa, con', inp', err' { _expected = HashSet.insert expect $ _expected err' }#)

notFollowedBy :: Parser Text -> Parser ()
notFollowedBy (Parser p) =
  Parser \con inp err lineCol base ->
    case p con inp err lineCol base of
      OK a _ _ _ ->
        Fail con inp $ err <> failed ("Unexpected '" <> a <> "'")

      Fail {} ->
        OK () con inp err

notFollowedByToken :: UnspannedToken -> Parser ()
notFollowedByToken token_ =
  notFollowedBy $ Lexer.displayToken token_ <$ token token_

withRecovery :: (ErrorReason -> Position.Absolute -> [Token] -> Parser a) -> Parser a -> Parser a
withRecovery recover_ (Parser p) =
  Parser \con inp err lineCol base ->
    case p con inp err lineCol base of
      ok@OK {} ->
        ok

      f@(Fail _con inp' err') ->
        case unParser (recover_ err' base inp') con inp err lineCol base of
          ok@OK {} ->
            ok

          Fail {} ->
            f

withToken
  ::
    (forall (r :: TYPE ResultRep)
    . (a -> r)
    -> (ErrorReason -> r)
    -> Span.Relative
    -> UnspannedToken
    -> r
    )
  -> Parser a
withToken f =
  Parser \con inp err _lineCol base ->
    case inp of
      [] ->
        Fail con inp $ err <> failed "Unexpected EOF"

      Token _pos tokenSpan token_:inp' ->
        f
          (\a -> OK a ConsumedSome inp' mempty)
          (Fail con inp)
          (Span.relativeTo base tokenSpan)
          token_

withIndentedToken
  ::
    (forall (r :: TYPE ResultRep)
    . (a -> r)
    -> (ErrorReason -> r)
    -> Span.Relative
    -> UnspannedToken
    -> r
    )
  -> Parser a
withIndentedToken f =
  Parser \con inp err (Position.LineColumn line col) base ->
    case inp of
      [] ->
        Fail con inp $ err <> failed "Unexpected EOF"

      Token (Position.LineColumn tokenLine tokenCol) tokenSpan token_:inp'
        | line == tokenLine || col < tokenCol ->
          f
            (\a -> OK a ConsumedSome inp' mempty)
            (\err' -> Fail con inp $ err <> err')
            (Span.relativeTo base tokenSpan)
            token_

        | otherwise ->
          Fail con inp $ err <> failed "Unexpected unindent"

withIndentedTokenM
  ::
    (forall (r :: TYPE ResultRep)
    . (Parser a -> r)
    -> r
    -> Span.Relative
    -> UnspannedToken
    -> r
    )
  -> Parser a
withIndentedTokenM f =
  Parser \con inp err lineCol@(Position.LineColumn line col) base ->
    case inp of
      [] ->
        Fail con inp $ err <> failed "Unexpected EOF"

      Token (Position.LineColumn tokenLine tokenCol) tokenSpan token_:inp'
        | line == tokenLine || col < tokenCol ->
          f
            (\pa -> unParser pa ConsumedSome inp' mempty lineCol base)
            (Fail con inp err)
            (Span.relativeTo base tokenSpan)
            token_

        | otherwise ->
          Fail con inp $ err <> failed "Unexpected unindent"

withIndentationBlock :: Parser a -> Parser a
withIndentationBlock (Parser p) =
  Parser \pos inp err lineCol base ->
    case inp of
      [] ->
        p pos inp err lineCol base

      Token tokenLineCol _ _:_ ->
        p pos inp err tokenLineCol base

relativeTo :: Parser a -> Parser (Position.Absolute, a)
relativeTo (Parser p) =
  Parser \con inp err lineCol _base ->
    case inp of
      [] ->
        Fail con inp $ err <> failed "Unexpected EOF"

      Token _ (Span.Absolute tokenStart _) _:_ ->
        mapResult ((,) tokenStart) (p con inp err lineCol tokenStart)

sameLevel :: Parser a -> Parser a
sameLevel (Parser p) =
  Parser \con inp err lineCol@(Position.LineColumn _ col) base ->
    case inp of
      [] ->
        Fail con inp $ err <> failed "Unexpected EOF"

      Token (Position.LineColumn _ tokenCol) _ _:_
        | col == tokenCol ->
          p con inp err lineCol base

        | col > tokenCol ->
          Fail con inp $ err <> failed "Unexpected unindent"

        | otherwise ->
          Fail con inp $ err <> failed "Unexpected indent"

indented :: Parser a -> Parser a
indented (Parser p) =
  Parser \con inp err lineCol@(Position.LineColumn line col) base ->
    case inp of
      [] ->
        Fail con inp $ err <> failed "Unexpected EOF"

      Token (Position.LineColumn tokenLine tokenCol) _ _:_
        | line == tokenLine || col < tokenCol ->
          p con inp err lineCol base

        | otherwise ->
          Fail con inp $ err <> failed "Unexpected unindent"

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

spannedModuleName :: Parser (Span.Relative, Name.Module)
spannedModuleName =
  second Name.Module <$> spannedIdentifier

spannedName :: Parser Surface.SpannedName
spannedName =
  uncurry Surface.SpannedName . second Name.Surface <$> spannedIdentifier

spannedConstructor :: Parser (Span.Relative, Name.Constructor)
spannedConstructor =
  second Name.Constructor <$> spannedIdentifier

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
  Parser \con inp err (Position.LineColumn line col) _base ->
    case inp of
      _:inp' ->
        OK () ConsumedSome (dropWhile (\(Token (Position.LineColumn tokenLine tokenCol) _ _) -> line == tokenLine || col < tokenCol) inp') mempty

      _ ->
        Fail con inp $ err <> failed "Unexpected EOF"

-------------------------------------------------------------------------------
-- Patterns

atomicPattern :: Parser Surface.Pattern
atomicPattern =
  (<?> "pattern") $
    withIndentedTokenM \continue break span token_ ->
      case token_ of
        Lexer.LeftParen ->
          continue $ pattern_ <* token Lexer.RightParen

        Lexer.QuestionMark ->
          continue $ pure $ Surface.Pattern span $ Surface.ConOrVar (Surface.SpannedName span "?") mempty

        Lexer.Underscore ->
          continue $ pure $ Surface.Pattern span Surface.WildcardPattern

        Lexer.Forced ->
          continue $ (\term_@(Surface.Term termSpan _) -> Surface.Pattern termSpan $ Surface.Forced term_) <$> atomicTerm

        Lexer.Identifier name_ ->
          continue $ pure $ Surface.Pattern span $ Surface.ConOrVar (Surface.SpannedName span $ Name.Surface name_) mempty

        Lexer.Number int ->
          continue $ pure $ Surface.Pattern span $ Surface.LitPattern $ Literal.Integer int

        _ ->
          break

pattern_ :: Parser Surface.Pattern
pattern_ =
  ( Surface.conOrVar <$> spannedName <*> many plicitPattern
    <|> atomicPattern
  )
  <**>
  ( flip Surface.anno <$ token Lexer.Colon <*> term
    <|> pure identity
  ) <?> "pattern"

plicitPattern :: Parser Surface.PlicitPattern
plicitPattern =
  mkImplicitPattern <$>
    token Lexer.LeftImplicitBrace <*>
    sepBy patName (token $ Lexer.Operator ",") <*>
    token Lexer.RightImplicitBrace
  <|> Surface.ExplicitPattern <$> atomicPattern
  <?> "explicit or implicit pattern"
  where
    mkImplicitPattern span1 pats span2 =
      Surface.ImplicitPattern (Span.add span1 span2) $ HashMap.fromList pats
    patName =
      spannedIdentifier <**>
        ((\pat (_, nameText) -> (Name nameText, pat)) <$ token Lexer.Equals <*> pattern_
        <|> pure (\(span, nameText) -> (Name nameText, Surface.Pattern span $ Surface.ConOrVar (Surface.SpannedName span (Name.Surface nameText)) mempty))
        )

-------------------------------------------------------------------------------
-- Terms

recoveringTerm :: Parser Surface.Term
recoveringTerm =
  withRecovery
    (\errorInfo base inp' -> 
      case inp' of
        Token _ tokenSpan _:_ ->
          recover (Surface.Term (Span.relativeTo base tokenSpan) . Surface.ParseError) errorInfo base inp'

        _ ->
          empty
    )
    term

atomicTerm :: Parser Surface.Term
atomicTerm =
  (<?> "term") $
    withIndentedTokenM $ \continue break span token_ ->
      case token_ of
        Lexer.LeftParen ->
          continue $ term <* token Lexer.RightParen

        Lexer.Let ->
          continue $ Surface.lets <$> blockOfMany let_ <* token Lexer.In <*> term

        Lexer.Underscore ->
          continue $ pure $ Surface.Term span Surface.Wildcard

        Lexer.QuestionMark ->
          continue $ pure $ Surface.Term span Surface.Wildcard

        Lexer.Identifier ident ->
          continue $ pure $ Surface.Term span $ Surface.Var $ Name.Surface ident

        Lexer.Case ->
          continue $
            Surface.case_ span <$> term <*> token Lexer.Of <*> blockOfMany branch

        Lexer.Lambda ->
          continue $
            Surface.lams <$> some plicitPattern <* token Lexer.Dot <*> term

        Lexer.Forall ->
          continue $
            Surface.pis Implicit <$>
              some
                ( (,) <$ token Lexer.LeftParen <*> some spannedName <* token Lexer.Colon <*> term <* token Lexer.RightParen
                <|> (\spannedName_@(Surface.SpannedName span_ _) -> ([spannedName_], Surface.Term span_ Surface.Wildcard)) <$> spannedName
                )
                <* token Lexer.Dot <*> term

        Lexer.Number int ->
          continue $ pure $ Surface.Term span $ Surface.Lit $ Literal.Integer int

        _ ->
          break
  where
    branch :: Parser (Surface.Pattern, Surface.Term)
    branch =
      (,) <$> pattern_ <* token Lexer.RightArrow <*> term

let_ :: Parser Surface.Let
let_ = do
  (span, nameText) <- spannedIdentifier
  Surface.LetType (Surface.SpannedName span $ Name.Surface nameText) <$ token Lexer.Colon <*> recoveringTerm
    <|> Surface.Let (Name.Surface nameText) <$> clauses span nameText
  <?> "let binding"

plicitAtomicTerm :: Parser (Surface.Term -> Surface.Term)
plicitAtomicTerm =
  (\args span fun -> Surface.implicitApp fun (HashMap.fromList args) span) <$ token Lexer.LeftImplicitBrace <*>
    sepBy implicitArgument (token $ Lexer.Operator ",") <*>
    token Lexer.RightImplicitBrace
  <|> flip Surface.app <$> atomicTerm
  where
    implicitArgument =
      spannedIdentifier <**>
        ((\t (_, nameText) -> (Name nameText, t)) <$ token Lexer.Equals <*> term
        <|> pure (\(span, nameText) -> (Name nameText, Surface.Term span $ Surface.Var $ Name.Surface nameText))
        )

term :: Parser Surface.Term
term =
  Surface.pis Explicit <$>
    some
      ((,) <$> try (token Lexer.LeftParen *> some spannedName <* token Lexer.Colon) <*>
        term <* token Lexer.RightParen
      ) <*
    token Lexer.RightArrow <*> term
  <|> atomicTerm <**> (foldl' (flip (.)) identity <$> many plicitAtomicTerm) <**> fun
  <?> "term"
  where
    fun =
      flip Surface.function <$ token Lexer.RightArrow <*> term
      <|> pure identity

-------------------------------------------------------------------------------
-- Definitions

definition :: Parser (Either Error.Parsing (Position.Absolute, (Name, Surface.Definition)))
definition =
  withRecovery (recover Left) $
  fmap Right $
  sameLevel $
  withIndentationBlock $
  relativeTo $
    dataDefinition
    <|> do
      (span, nameText) <- spannedIdentifier
      (,) (Name nameText) <$>
        (Surface.TypeDeclaration span <$ token Lexer.Colon <*> recoveringTerm
        <|> Surface.ConstantDefinition <$> clauses span nameText
        )
    <?> "definition"

clauses :: Span.Relative -> Text -> Parser [(Span.Relative, Surface.Clause)]
clauses firstSpan nameText =
  (:) <$>
    ((,) firstSpan <$> clause) <*>
    manySame ((,) <$> try (token (Lexer.Identifier nameText) <* notFollowedByToken Lexer.Colon) <*> clause)

clause :: Parser Surface.Clause
clause =
  Surface.clause <$> many plicitPattern <*> token Lexer.Equals <*> recoveringTerm

dataDefinition :: Parser (Name, Surface.Definition)
dataDefinition =
  mkDataDefinition <$> boxity <*> spannedIdentifier <*> parameters <*>
    (token Lexer.Where *> blockOfMany gadtConstructors
    <|> token Lexer.Equals *> sepBy1 adtConstructor (token Lexer.Pipe)
    )
  where
    boxity =
      Boxed <$ token (Lexer.Identifier "boxed") <* uncheckedToken Lexer.Data
      <|> Unboxed <$ token Lexer.Data

    mkDataDefinition boxity_ (span, nameText) params constrs =
      (Name nameText, Surface.DataDefinition span boxity_ params constrs)
    parameters =
      parameters1 <|> pure []

    parameters1 =
      implicitParameters
      <|> (<>) <$> explicitParameter <*> parameters

    explicitParameter =
      (\spannedNames type_ -> [(spannedName_, type_, Explicit) | spannedName_ <- spannedNames]) <$ token Lexer.LeftParen <*> some spannedName <* token Lexer.Colon <*> recoveringTerm <* token Lexer.RightParen
      <|> (\spannedName_@(Surface.SpannedName span _) -> pure (spannedName_, Surface.Term span Surface.Wildcard, Explicit)) <$> spannedName

    implicitParameters =
      (<>) . concat <$ token Lexer.Forall <*>
        some
          ((\spannedNames type_ -> [(spannedName_, type_, Implicit) | spannedName_ <- spannedNames]) <$ token Lexer.LeftParen <*> some spannedName <* token Lexer.Colon <*> term <* token Lexer.RightParen
          <|> (\spannedName_@(Surface.SpannedName span _) -> [(spannedName_, Surface.Term span Surface.Wildcard, Implicit)]) <$> spannedName
          ) <* token Lexer.Dot <*> parameters1

    gadtConstructors =
      withIndentationBlock $
        Surface.GADTConstructors <$> some spannedConstructor <* token Lexer.Colon <*> recoveringTerm

    adtConstructor =
      uncurry Surface.ADTConstructor <$> spannedConstructor <*> many atomicTerm

-------------------------------------------------------------------------------
-- Module

module_ :: Parser ((Maybe (Span.Absolute, Name.Module), Module.Header), [Either Error.Parsing (Position.Absolute, (Name, Surface.Definition))])
module_ =
  withIndentationBlock $
    (,) <$> moduleHeader <*> manySame definition

moduleHeader :: Parser (Maybe (Span.Absolute, Name.Module), Module.Header)
moduleHeader =
  mkModuleHeader <$> moduleExposing <*> manySame import_
  where
    mkModuleHeader (mname, exposed) imports =
      (mname, Module.Header exposed imports)
    moduleExposing =
      sameLevel (withIndentationBlock $ (\(span, name) exposed -> (Just (Span.absoluteFrom 0 span, name), exposed)) <$ token (Lexer.Identifier "module") <*> spannedModuleName <* token (Lexer.Identifier "exposing") <*> exposedNames)
      <|> pure (Nothing, Module.AllExposed)

import_ :: Parser Module.Import
import_ =
  sameLevel $
  withIndentationBlock $
    mkImport
      <$ token (Lexer.Identifier "import") <*> spannedModuleName
      <*>
        (Just <$ token (Lexer.Identifier "as") <*> spannedName
        <|> pure Nothing
        )
      <*>
        (token (Lexer.Identifier "exposing") *> exposedNames
        <|> pure mempty
        )
  where
    mkImport (span, n@(Name.Module text)) malias exposed =
      Module.Import
        { _span = absoluteSpan
        , _module = n
        , _alias =
          maybe
            (absoluteSpan, Name.Surface text)
            (\(Surface.SpannedName span' name) -> (Span.absoluteFrom 0 span', name))
            malias
        , _importedNames = exposed
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
      <|> Module.Exposed . HashSet.fromList <$> sepBy ((\(Surface.SpannedName _ name) -> name) <$> spannedName) (token $ Lexer.Operator ",")
