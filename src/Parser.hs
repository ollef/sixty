{-# language BlockArguments #-}
{-# language DataKinds #-}
{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language PolyKinds #-}
{-# language RankNTypes #-}
{-# language TupleSections #-}
{-# language UnboxedTuples #-}
{-# language ViewPatterns #-}
module Parser where

import Protolude hiding (break, try, moduleName, Option)

import Control.Monad.Fail
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import GHC.Exts hiding (toList)
import qualified Data.ByteString.Internal as ByteString
import GHC.ForeignPtr (ForeignPtr(..))
import Text.Parser.Combinators (sepBy, sepBy1)

import Boxity
import qualified Error.Parsing as Error
import qualified Lexer2 as Lexer
import Lexer2 (TokenList(..), InnerToken(..))
import qualified Literal
import qualified Module
import Name (Name(Name))
import qualified Name
import Plicity
import qualified Position
import qualified Span
import qualified Surface.Syntax as Surface

parseByteString :: Parser a -> ByteString -> Either Error.Parsing a
parseByteString parser bs@(ByteString.PS source _ _) =
  parseTokens parser source $ Lexer.lexByteString bs

parseTokens :: Parser a -> ForeignPtr Word8 -> TokenList -> Either Error.Parsing a
parseTokens p source tokens =
  case unParser p source tokens mempty (Position.LineColumn 0 0) (Position.Absolute 0) of
    OK a _ _ _ ->
      Right a

    Fail _ tokens' err ->
      Left Error.Parsing
        { Error.reason = _reason err
        , Error.expected = toList $ _expected err
        , Error.position =
          case tokens' of
            Empty ->
              Left Error.EOF

            Token _ _ (Span.Absolute pos _) _ ->
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
    :: ForeignPtr Word8 -- input source
    -> TokenList -- input tokens
    -> ErrorReason -- previous errors at this position
    -> Position.LineColumn -- indentation base
    -> Position.Absolute -- base position
    -> Result a
  }

type Consumed = (# (##) | (##) #)

pattern ConsumedNone :: Consumed
pattern ConsumedNone = (# (##) | #)
pattern ConsumedSome :: Consumed
pattern ConsumedSome = (# | (##) #)

{-# complete ConsumedNone, ConsumedSome #-}

type Option a = (# a | (##) #)

pattern Some :: a -> Option a
pattern Some a = (# a | #)

pattern None :: Option a
pattern None = (# | (##) #)

{-# complete Some, None #-}

type Result a = (# Option a, Consumed, TokenList, ErrorReason #)
type ResultRep = 'TupleRep '[ 'SumRep '[ 'LiftedRep, 'TupleRep '[]], 'SumRep '[ 'TupleRep '[], 'TupleRep '[]], 'LiftedRep, 'LiftedRep ]

pattern OK :: a -> Consumed -> TokenList -> ErrorReason -> Result a
pattern OK a con inp err = (# Some a, con, inp, err #)

pattern Fail :: Consumed -> TokenList -> ErrorReason -> Result a
pattern Fail con inp err = (# None, con, inp, err #)

{-# inline consumedAtLeast #-}
consumedAtLeast :: Consumed -> Result a -> Result a
consumedAtLeast consumed result =
  case consumed of
    ConsumedNone -> result
    ConsumedSome -> consumedSome result

{-# inline consumedSome #-}
consumedSome :: Result a -> Result a
consumedSome (# res, _, inp, err #) = (# res, ConsumedSome, inp, err #)

{-# complete OK, Fail #-}

{-# inline mapResult #-}
mapResult :: (a -> b) -> Result a -> Result b
mapResult f (OK a con inp err) = OK (f a) con inp err
mapResult _ (Fail con inp err) = Fail con inp err

{-# inline setResult #-}
setResult :: b -> Result a -> Result b
setResult b (OK _ con inp err) = OK b con inp err
setResult _ (Fail con inp err) = Fail con inp err

instance Functor Parser where
  {-# inline fmap #-}
  fmap f (Parser p) =
    Parser \source inp err lineCol base ->
      mapResult f (p source inp err lineCol base)

instance Applicative Parser where
  {-# inline pure #-}
  pure a =
    Parser \_ inp err _ _ -> OK a ConsumedNone inp err

  {-# inline (<*>) #-}
  Parser p <*> Parser q =
    Parser $ \source inp err lineCol base ->
      case p source inp err lineCol base of
        OK f con inp' err' ->
          consumedAtLeast con (mapResult f (q source inp' err' lineCol base))

        Fail con inp' err' ->
          Fail con inp' err'

  {-# inline (*>) #-}
  Parser p *> Parser q =
    Parser $ \source inp err lineCol base ->
      case p source inp err lineCol base of
        OK _ con inp' err' ->
          consumedAtLeast con (q source inp' err' lineCol base)

        Fail con inp' err' ->
          Fail con inp' err'

  {-# inline (<*) #-}
  Parser p <* Parser q =
    Parser $ \source inp err lineCol base ->
      case p source inp err lineCol base of
        OK a con inp' err' ->
          consumedAtLeast con (setResult a (q source inp' err' lineCol base))

        f ->
          f

instance Alternative Parser where
  {-# inline empty #-}
  empty =
    Parser \_ inp err _ _ -> Fail ConsumedNone inp err

  {-# inline (<|>) #-}
  Parser p <|> Parser q =
    Parser \source inp err lineCol base ->
      case p source inp err lineCol base of
        result@OK {} ->
          result

        Fail ConsumedNone _inp err' ->
          q source inp err' lineCol base

        f@(Fail ConsumedSome _ _) ->
          f

instance Monad Parser where
  {-# inline (>>=) #-}
  Parser p >>= f =
    Parser \source inp err lineCol base ->
      case p source inp err lineCol base of
        OK a con inp' err' ->
          consumedAtLeast con (unParser (f a) source inp' err' lineCol base)

        Fail con inp' err' ->
          Fail con inp' err'

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
  Parser \_ inp err' _ _ -> Fail ConsumedNone inp $ err' <> err

try :: Parser a -> Parser a
try (Parser p) =
  Parser \source inp err lineCol base ->
    case p source inp err lineCol base of
      ok@OK {} ->
        ok

      Fail {} ->
        Fail ConsumedNone inp err

(<?>) :: Parser a -> Text -> Parser a
Parser p <?> expect =
  Parser \source inp err lineCol base ->
    case p source inp err lineCol base of
      (# oa, con, inp', err' #) ->
        (# oa, con, inp', err' { _expected = HashSet.insert expect $ _expected err' }#)

notFollowedBy :: Parser Text -> Parser ()
notFollowedBy (Parser p) =
  Parser \source inp err lineCol base ->
    case p source inp err lineCol base of
      OK a _ _ _ ->
        Fail ConsumedNone inp $ err <> failed ("Unexpected '" <> a <> "'")

      Fail {} ->
        OK () ConsumedNone inp err

notFollowedByToken0 :: InnerToken -> Parser ()
notFollowedByToken0 token_ =
  notFollowedBy $ Lexer.displayToken token_ "" <$ token0 token_

{-# inline withRecovery #-}
withRecovery :: (ErrorReason -> Position.Absolute -> TokenList -> Parser a) -> Parser a -> Parser a
withRecovery recover_ (Parser p) =
  Parser \source inp err lineCol base ->
    case p source inp err lineCol base of
      ok@OK {} ->
        ok

      f@(Fail _con inp' err') ->
        case unParser (recover_ err' base inp') source inp err lineCol base of
          ok@OK {} ->
            ok

          Fail {} ->
            f

{-# inline withToken #-}
withToken
  ::
    (forall (r :: TYPE ResultRep)
    . (a -> r)
    -> (ErrorReason -> r)
    -> Span.Relative
    -> InnerToken
    -> r
    )
  -> Parser a
withToken f =
  Parser \_ inp err _lineCol base ->
    case inp of
      Empty ->
        Fail ConsumedNone inp $ err <> failed "Unexpected EOF"

      Token tok _pos span inp' ->
        f
          (\a -> OK a ConsumedSome inp' mempty)
          (Fail ConsumedNone inp)
          (Span.relativeTo base span)
          tok

{-# inline withIndentedToken #-}
withIndentedToken
  ::
    (forall (r :: TYPE ResultRep)
    . (a -> r)
    -> (ErrorReason -> r)
    -> Span.Relative
    -> InnerToken
    -> ByteString
    -> r
    )
  -> Parser a
withIndentedToken f =
  Parser \source inp err (Position.LineColumn line col) base ->
    case inp of
      Empty ->
        Fail ConsumedNone inp $ err <> failed "Unexpected EOF"

      Token tok (Position.LineColumn tokenLine tokenCol) tokenSpan inp'
        | line == tokenLine || col < tokenCol ->
          f
            (\a -> OK a ConsumedSome inp' mempty)
            (\err' -> Fail ConsumedNone inp $ err <> err')
            (Span.relativeTo base tokenSpan)
            tok
            (Lexer.toByteString source tokenSpan)

        | otherwise ->
          Fail ConsumedNone inp $ err <> failed "Unexpected unindent"

{-# inline withIndentedTokenM #-}
withIndentedTokenM
  ::
    (forall (r :: TYPE ResultRep)
    . (Parser a -> r)
    -> (ErrorReason -> r)
    -> Span.Relative
    -> InnerToken
    -> ByteString
    -> r
    )
  -> Parser a
withIndentedTokenM f =
  Parser \source inp err lineCol@(Position.LineColumn line col) base ->
    case inp of
      Empty ->
        Fail ConsumedNone inp $ err <> failed "Unexpected EOF"

      Token tok (Position.LineColumn tokenLine tokenCol) tokenSpan inp'
        | line == tokenLine || col < tokenCol ->
          f
            (\pa -> consumedSome (unParser pa source inp' mempty lineCol base))
            (\err' -> Fail ConsumedNone inp $ err <> err')
            (Span.relativeTo base tokenSpan)
            tok
            (Lexer.toByteString source tokenSpan)

        | otherwise ->
          Fail ConsumedNone inp $ err <> failed "Unexpected unindent"

{-# inline withIndentationBlock #-}
withIndentationBlock :: Parser a -> Parser a
withIndentationBlock (Parser p) =
  Parser \source inp err lineCol base ->
    case inp of
      Empty ->
        p source inp err lineCol base

      Token _ tokenLineCol _ _ ->
        p source inp err tokenLineCol base

{-# inline relativeTo #-}
relativeTo :: Parser a -> Parser (Position.Absolute, a)
relativeTo (Parser p) =
  Parser \source inp err lineCol _base ->
    case inp of
      Empty ->
        Fail ConsumedNone inp $ err <> failed "Unexpected EOF"

      Token _ _ (Span.Absolute tokenStart _) _ ->
        mapResult (tokenStart, ) (p source inp err lineCol tokenStart)

{-# inline sameLevel #-}
sameLevel :: Parser a -> Parser a
sameLevel (Parser p) =
  Parser \source inp err lineCol@(Position.LineColumn _ col) base ->
    case inp of
      Empty ->
        Fail ConsumedNone inp $ err <> failed "Unexpected EOF"

      Token _ (Position.LineColumn _ tokenCol) _ _
        | col == tokenCol ->
          p source inp err lineCol base

        | col > tokenCol ->
          Fail ConsumedNone inp $ err <> failed "Unexpected unindent"

        | otherwise ->
          Fail ConsumedNone inp $ err <> failed "Unexpected indent"

{-# inline indented #-}
indented :: Parser a -> Parser a
indented (Parser p) =
  Parser \source inp err lineCol@(Position.LineColumn line col) base ->
    case inp of
      Empty ->
        Fail ConsumedNone inp $ err <> failed "Unexpected EOF"

      Token _ (Position.LineColumn tokenLine tokenCol) _ _
        | line == tokenLine || col < tokenCol ->
          p source inp err lineCol base

        | otherwise ->
          Fail ConsumedNone inp $ err <> failed "Unexpected unindent"

{-# inline someSame #-}
-- | One or more at the same indentation level.
someSame :: Parser a -> Parser [a]
someSame p =
  some (sameLevel $ withIndentationBlock p)

{-# inline manySame #-}
-- | Zero or more at the same indentation level.
manySame :: Parser a -> Parser [a]
manySame p =
  many (sameLevel $ withIndentationBlock p)

{-# inline blockOfMany #-}
blockOfMany :: Parser a -> Parser [a]
blockOfMany p =
  indented (withIndentationBlock $ someSame p)
  <|> pure []

{-# inline token0 #-}
token0 :: InnerToken -> Parser Span.Relative
token0 t =
  withIndentedToken $ \continue break span t' _ ->
    if t == t' then
      continue span

    else
      break $ expected $ "'" <> Lexer.displayToken t "" <> "'"

{-# inline token #-}
token :: InnerToken -> ByteString -> Parser Span.Relative
token t bs =
  withIndentedToken $ \continue break span t' bs' ->
    if t == t' && bs == bs' then
      continue span

    else
      break $ expected $ "'" <> Lexer.displayToken t bs <> "'"

{-# inline uncheckedToken0 #-}
uncheckedToken0 :: InnerToken -> Parser Span.Relative
uncheckedToken0 t =
  withToken $ \continue break span t' ->
    if t == t' then
      continue span

    else
      break $ expected $ "'" <> Lexer.displayToken t "" <> "'"

{-# inline spannedIdentifier #-}
spannedIdentifier :: Parser (Span.Relative, ByteString)
spannedIdentifier =
  withIndentedToken $ \continue break span token_ name_ ->
    case token_ of
      Lexer.Identifier ->
        continue (span, name_)

      _ ->
        break $ expected "identifier"

{-# inline spannedModuleName #-}
spannedModuleName :: Parser (Span.Relative, Name.Module)
spannedModuleName =
  second Name.Module <$> spannedIdentifier

{-# inline spannedName #-}
spannedName :: Parser Surface.SpannedName
spannedName =
  uncurry Surface.SpannedName . second Name.Surface <$> spannedIdentifier

{-# inline spannedConstructor #-}
spannedConstructor :: Parser (Span.Relative, Name.Constructor)
spannedConstructor =
  second Name.Constructor <$> spannedIdentifier

-------------------------------------------------------------------------------
-- Error recovery

recover :: (Error.Parsing -> a) -> ErrorReason -> Position.Absolute -> TokenList -> Parser a
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
        Token _ _ (Span.Absolute startPos _) _ ->
          Right startPos

        Empty ->
          Left Error.EOF

skipToBaseLevel :: Parser ()
skipToBaseLevel =
  Parser \_ inp err (Position.LineColumn line col) _base ->
    case inp of
      Token _ _ _ inp' -> do
        let
          go Empty = Empty
          go inp''@(Token _ (Position.LineColumn tokenLine tokenCol) _ inp''')
            | line == tokenLine || col < tokenCol =
              go inp'''
            | otherwise =
              inp''
        OK () ConsumedSome (go inp') mempty

      Empty ->
        Fail ConsumedNone inp $ err <> failed "Unexpected EOF"

-------------------------------------------------------------------------------
-- Patterns

atomicPattern :: Parser Surface.Pattern
atomicPattern =
  withIndentedTokenM \continue break span token_ bs ->
    case token_ of
      Lexer.LeftParen ->
        continue $ pattern_ <* token0 Lexer.RightParen

      Lexer.QuestionMark ->
        continue $ pure $ Surface.Pattern span $ Surface.ConOrVar (Surface.SpannedName span "?") mempty

      Lexer.Underscore ->
        continue $ pure $ Surface.Pattern span Surface.WildcardPattern

      Lexer.Forced ->
        continue $ (\term_@(Surface.Term termSpan _) -> Surface.Pattern (Span.add span termSpan) $ Surface.Forced term_) <$> atomicTerm

      Lexer.Identifier ->
        continue $ pure $ Surface.Pattern span $ Surface.ConOrVar (Surface.SpannedName span $ Name.Surface bs) mempty

      Lexer.Number ->
        continue $ pure $ Surface.Pattern span $ Surface.LitPattern $ Literal.Integer $ Lexer.parseNumber bs

      _ ->
        break $ expected "pattern"

pattern_ :: Parser Surface.Pattern
pattern_ =
  ( Surface.conOrVar <$> spannedName <*> many plicitPattern
    <|> atomicPattern
  )
  <**>
  ( flip Surface.anno <$ token0 Lexer.Colon <*> term
    <|> pure identity
  ) <?> "pattern"

plicitPattern :: Parser Surface.PlicitPattern
plicitPattern =
  mkImplicitPattern <$>
    token0 Lexer.LeftImplicitBrace <*>
    sepBy patName (token Lexer.Operator ",") <*>
    token0 Lexer.RightImplicitBrace
  <|> Surface.ExplicitPattern <$> atomicPattern
  <?> "explicit or implicit pattern"
  where
    mkImplicitPattern span1 pats span2 =
      Surface.ImplicitPattern (Span.add span1 span2) $ HashMap.fromList pats
    patName =
      spannedIdentifier <**>
        ((\pat (_, nameText) -> (Name nameText, pat)) <$ token0 Lexer.Equals <*> pattern_
        <|> pure (\(span, nameText) -> (Name nameText, Surface.Pattern span $ Surface.ConOrVar (Surface.SpannedName span (Name.Surface nameText)) mempty))
        )

-------------------------------------------------------------------------------
-- Terms

recoveringTerm :: Parser Surface.Term
recoveringTerm =
  withRecovery
    (\errorInfo base inp' ->
      case inp' of
        Token _ _ tokenSpan _ ->
          recover (Surface.Term (Span.relativeTo base tokenSpan) . Surface.ParseError) errorInfo base inp'

        Empty ->
          empty
    )
    term

atomicTerm :: Parser Surface.Term
atomicTerm =
  withIndentedTokenM $ \continue break span token_ bs ->
    case token_ of
      Lexer.LeftParen ->
        continue $ term <* token0 Lexer.RightParen

      Lexer.Let ->
        continue $ Surface.lets span <$> blockOfMany let_ <* token0 Lexer.In <*> term

      Lexer.Underscore ->
        continue $ pure $ Surface.Term span Surface.Wildcard

      Lexer.QuestionMark ->
        continue $ pure $ Surface.Term span Surface.Wildcard

      Lexer.Identifier ->
        continue $ pure $ Surface.Term span $ Surface.Var $ Name.Surface bs

      Lexer.Case ->
        continue $
          Surface.case_ span <$> term <*> token0 Lexer.Of <*> blockOfMany branch

      Lexer.Lambda ->
        continue $
          Surface.lams span <$> some plicitPattern <* token0 Lexer.Dot <*> term

      Lexer.Forall ->
        continue $
          Surface.implicitPis span <$>
            some
              ( (,,) <$> token0 Lexer.LeftParen <*> some spannedName <* token0 Lexer.Colon <*> term <* token0 Lexer.RightParen
              <|> (\spannedName_@(Surface.SpannedName span_ _) -> (span_, [spannedName_], Surface.Term span_ Surface.Wildcard)) <$> spannedName
              )
              <* token0 Lexer.Dot <*> term

      Lexer.Number ->
        continue $ pure $ Surface.Term span $ Surface.Lit $ Literal.Integer $ Lexer.parseNumber bs

      _ ->
        break $ expected "term"
  where
    branch :: Parser (Surface.Pattern, Surface.Term)
    branch =
      (,) <$> pattern_ <* token0 Lexer.RightArrow <*> term

let_ :: Parser Surface.Let
let_ = do
  (span, nameText) <- spannedIdentifier
  Surface.LetType (Surface.SpannedName span $ Name.Surface nameText) <$ token0 Lexer.Colon <*> recoveringTerm
    <|> Surface.Let (Name.Surface nameText) <$> clauses span nameText
  <?> "let binding"

plicitAtomicTerm :: Parser (Surface.Term -> Surface.Term)
plicitAtomicTerm =
  (\args span fun -> Surface.implicitApp fun (HashMap.fromList args) span) <$ token0 Lexer.LeftImplicitBrace <*>
    sepBy implicitArgument (token Lexer.Operator ",") <*>
    token0 Lexer.RightImplicitBrace
  <|> flip Surface.app <$> atomicTerm
  where
    implicitArgument =
      spannedIdentifier <**>
        ((\t (_, nameText) -> (Name nameText, t)) <$ token0 Lexer.Equals <*> term
        <|> pure (\(span, nameText) -> (Name nameText, Surface.Term span $ Surface.Var $ Name.Surface nameText))
        )

term :: Parser Surface.Term
term =
  Surface.pis Explicit <$> some typedBindings <* token0 Lexer.RightArrow <*> term
  <|> atomicTerm <**> (foldl' (flip (.)) identity <$> many plicitAtomicTerm) <**> fun
  <?> "term"
  where
    typedBindings =
      uncurry (,,) <$> try ((,) <$> token0 Lexer.LeftParen <*> some spannedName <* token0 Lexer.Colon) <*>
        term <* token0 Lexer.RightParen

    fun =
      flip Surface.function <$ token0 Lexer.RightArrow <*> term
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
        (Surface.TypeDeclaration span <$ token0 Lexer.Colon <*> recoveringTerm
        <|> Surface.ConstantDefinition <$> clauses span nameText
        )
    <?> "definition"

clauses :: Span.Relative -> ByteString -> Parser [(Span.Relative, Surface.Clause)]
clauses firstSpan nameText =
  (:) <$>
    ((,) firstSpan <$> clause) <*>
    manySame ((,) <$> try (token Lexer.Identifier nameText <* notFollowedByToken0 Lexer.Colon) <*> clause)

clause :: Parser Surface.Clause
clause =
  Surface.clause <$> many plicitPattern <*> token0 Lexer.Equals <*> recoveringTerm

dataDefinition :: Parser (Name, Surface.Definition)
dataDefinition =
  mkDataDefinition <$> boxity <*> spannedIdentifier <*> parameters <*>
    (token0 Lexer.Where *> blockOfMany gadtConstructors
    <|> token0 Lexer.Equals *> sepBy1 adtConstructor (token0 Lexer.Pipe)
    )
  where
    boxity =
      Boxed <$ token Lexer.Identifier "boxed" <* uncheckedToken0 Lexer.Data
      <|> Unboxed <$ token0 Lexer.Data

    mkDataDefinition boxity_ (span, nameText) params constrs =
      (Name nameText, Surface.DataDefinition span boxity_ params constrs)
    parameters =
      parameters1 <|> pure []

    parameters1 =
      implicitParameters
      <|> (<>) <$> explicitParameter <*> parameters

    explicitParameter =
      (\spannedNames type_ -> [(spannedName_, type_, Explicit) | spannedName_ <- spannedNames]) <$ token0 Lexer.LeftParen <*> some spannedName <* token0 Lexer.Colon <*> recoveringTerm <* token0 Lexer.RightParen
      <|> (\spannedName_@(Surface.SpannedName span _) -> pure (spannedName_, Surface.Term span Surface.Wildcard, Explicit)) <$> spannedName

    implicitParameters =
      (<>) . concat <$ token0 Lexer.Forall <*>
        some
          ((\spannedNames type_ -> [(spannedName_, type_, Implicit) | spannedName_ <- spannedNames]) <$ token0 Lexer.LeftParen <*> some spannedName <* token0 Lexer.Colon <*> term <* token0 Lexer.RightParen
          <|> (\spannedName_@(Surface.SpannedName span _) -> [(spannedName_, Surface.Term span Surface.Wildcard, Implicit)]) <$> spannedName
          ) <* token0 Lexer.Dot <*> parameters1

    gadtConstructors =
      withIndentationBlock $
        Surface.GADTConstructors <$> some spannedConstructor <* token0 Lexer.Colon <*> recoveringTerm

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
      sameLevel ((\(span, name) exposed -> (Just (Span.absoluteFrom 0 span, name), exposed)) <$ token Lexer.Identifier "module" <*> spannedModuleName <* token Lexer.Identifier "exposing" <*> exposedNames)
      <|> pure (Nothing, Module.AllExposed)

import_ :: Parser Module.Import
import_ =
  mkImport
    <$ token Lexer.Identifier "import" <*> spannedModuleName
    <*>
      (Just <$ token Lexer.Identifier "as" <*> spannedName
      <|> pure Nothing
      )
    <*>
      (token Lexer.Identifier "exposing" *> exposedNames
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
  token0 Lexer.LeftParen *> inner <* token0 Lexer.RightParen
  where
    inner =
      Module.AllExposed <$ token Lexer.Operator ".."
      <|> Module.Exposed . HashSet.fromList <$> sepBy ((\(Surface.SpannedName _ name) -> name) <$> spannedName) (token Lexer.Operator ",")
