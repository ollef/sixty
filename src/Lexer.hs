{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}

module Lexer (
  lexText,
  TokenList (..),
  UnspannedToken (..),
  displayToken,
) where

import qualified Data.Char as Char
import Data.Coerce
import Data.Text.Array (Array)
import qualified Data.Text.Array as Array
import qualified Data.Text.Internal as Text
import qualified Data.Text.Internal.Encoding.Utf8 as Utf8
import qualified Position
import Protolude hiding (State, ord, state)
import qualified Span
import qualified UTF8

data TokenList
  = Empty
  | Token !Position.LineColumn !Span.Absolute !UnspannedToken !TokenList
  deriving (Show, Generic, NFData)

data UnspannedToken
  = -- Identifiers
    Identifier !Text
  | -- Reserved identifiers
    Let
  | In
  | Data
  | Where
  | Forall
  | Case
  | Of
  | Underscore
  | -- Operators
    Operator !Text
  | -- Reserved operators
    Equals
  | Dot
  | Colon
  | Pipe
  | RightArrow
  | QuestionMark
  | Forced
  | -- Special
    Number !Integer
  | Lambda
  | LeftParen
  | RightParen
  | LeftImplicitBrace
  | RightImplicitBrace
  | Error
  deriving (Eq, Show, Generic, NFData)

displayToken :: UnspannedToken -> Text
displayToken token =
  case token of
    Identifier name -> name
    Let -> "let"
    In -> "in"
    Data -> "data"
    Where -> "where"
    Forall -> "forall"
    Case -> "case"
    Of -> "of"
    Underscore -> "_"
    Operator name -> name
    Equals -> "="
    Dot -> "."
    Colon -> ":"
    Pipe -> "|"
    RightArrow -> "->"
    QuestionMark -> "?"
    Forced -> "~"
    Number int -> show int
    Lambda -> "\\"
    LeftParen -> "("
    RightParen -> ")"
    LeftImplicitBrace -> "@{"
    RightImplicitBrace -> "}"
    Error -> "[error]"

lexText :: Text -> TokenList
lexText (Text.Text array offset length_) =
  lex
    State
      { input = array
      , position = coerce offset
      , lineColumn = Position.LineColumn 0 0
      , end = coerce $ offset + length_
      }

-------------------------------------------------------------------------------

data State = State
  { input :: !Array
  , position :: !Position.Absolute
  , lineColumn :: !Position.LineColumn
  , end :: !Position.Absolute
  }

{-# INLINE satisfy #-}
satisfy :: Word8 -> (Word8 -> Bool) -> (Char -> Bool) -> State -> Maybe Int
satisfy c satisfyASCII satisfyNonASCII State {..}
  | c < 128 = if satisfyASCII c then Just 1 else Nothing
  | otherwise =
      case Utf8.utf8LengthByLeader c of
        2 | position + 1 < end, satisfyNonASCII (Utf8.chr2 c (index input $ position + 1)) -> Just 2
        3 | position + 2 < end, satisfyNonASCII (Utf8.chr3 c (index input $ position + 1) (index input $ position + 2)) -> Just 3
        4 | position + 3 < end, satisfyNonASCII (Utf8.chr4 c (index input $ position + 1) (index input $ position + 2) (index input $ position + 3)) -> Just 4
        _ -> Nothing

incColumn :: Int -> State -> State
incColumn n state@State {..} = state {position = Position.add position (coerce n), lineColumn = Position.addColumns lineColumn (coerce n)}

lex :: State -> TokenList
lex state@State {..}
  | position >= end =
      Empty
  | otherwise =
      case index input position of
        -------------------------------------------------------------------------
        -- Parens
        [UTF8.unit1|(|] ->
          token1 LeftParen $ lex $ incColumn 1 state
        [UTF8.unit1|)|] ->
          token1 RightParen $ lex $ incColumn 1 state
        -------------------------------------------------------------------------
        -- Comments
        [UTF8.unit1|-|]
          | position + 1 < end
          , [UTF8.unit1|-|] <- index input (position + 1) ->
              singleLineComment $ incColumn 2 state
        [UTF8.unit1|{|]
          | position + 1 < end
          , [UTF8.unit1|-|] <- index input (position + 1) ->
              multiLineComment (incColumn 2 state) 1
        -------------------------------------------------------------------------
        -- Whitespace
        [UTF8.unit1| |] ->
          lex $ incColumn 1 state
        [UTF8.unit1|	|] ->
          lex $ incColumn 1 state
        [UTF8.unit1|
|] ->
            lex (incColumn 1 state) {lineColumn = Position.addLine lineColumn}
        -------------------------------------------------------------------------
        -- Number
        [UTF8.unit1|\|] ->
          token1 Lambda $ lex $ incColumn 1 state
        -------------------------------------------------------------------------
        -- Number
        [UTF8.unit1|-|]
          | position + 1 < end
          , c <- index input (position + 1)
          , isNumeric c ->
              number position lineColumn (incColumn 1 state) True (fromIntegral $ c - [UTF8.unit1|0|])
        c
          | isNumeric c ->
              number position lineColumn (incColumn 1 state) False (fromIntegral $ c - [UTF8.unit1|0|])
        -------------------------------------------------------------------------
        -- Implicit braces
        [UTF8.unit1|@|]
          | position + 1 < end
          , [UTF8.unit1|{|] <- index input (position + 1) ->
              token2 LeftImplicitBrace $ lex $ incColumn 2 state
        [UTF8.unit1|}|] ->
          token1 RightImplicitBrace $ lex $ incColumn 1 state
        -------------------------------------------------------------------------
        -- Operator or identifier
        c
          | Just n <- satisfy c isASCIIIdentifierStart Char.isAlpha state ->
              identifier position lineColumn $ incColumn n state
        c
          | Just n <- satisfy c isASCIIOperator (\c' -> Char.isSymbol c' || Char.isPunctuation c') state ->
              operator position lineColumn $ incColumn n state
        -------------------------------------------------------------------------
        -- Error
        _ ->
          token1 Error $ lex $ incColumn 1 state
  where
    token1 =
      Token lineColumn $ Span.Absolute position (position + 1)

    token2 =
      Token lineColumn $ Span.Absolute position (position + 2)

-------------------------------------------------------------------------------

index :: Array -> Position.Absolute -> Word8
index =
  coerce Array.unsafeIndex

isNumeric :: Word8 -> Bool
isNumeric c =
  [UTF8.unit1|0|] <= c && c <= [UTF8.unit1|9|]

isASCIIIdentifierStart :: Word8 -> Bool
isASCIIIdentifierStart c =
  [UTF8.unit1|a|] <= c && c <= [UTF8.unit1|z|]
    || [UTF8.unit1|A|] <= c && c <= [UTF8.unit1|Z|]
    || c == [UTF8.unit1|_|]

isASCIIIdentifierCont :: Word8 -> Bool
isASCIIIdentifierCont c =
  isASCIIIdentifierStart c
    || isNumeric c
    || c == [UTF8.unit1|'|]

isASCIIOperator :: Word8 -> Bool
isASCIIOperator c =
  case c of
    [UTF8.unit1|!|] -> True
    [UTF8.unit1|#|] -> True
    [UTF8.unit1|$|] -> True
    [UTF8.unit1|%|] -> True
    [UTF8.unit1|&|] -> True
    [UTF8.unit1|*|] -> True
    [UTF8.unit1|+|] -> True
    [UTF8.unit1|,|] -> True
    [UTF8.unit1|-|] -> True
    [UTF8.unit1|.|] -> True
    [UTF8.unit1|/|] -> True
    [UTF8.unit1|:|] -> True
    [UTF8.unit1|;|] -> True
    [UTF8.unit1|<|] -> True
    [UTF8.unit1|=|] -> True
    [UTF8.unit1|>|] -> True
    [UTF8.unit1|?|] -> True
    [UTF8.unit1|@|] -> True
    [UTF8.unit1|\|] -> True
    [UTF8.unit1|^|] -> True
    [UTF8.unit1|`|] -> True
    [UTF8.unit1|||] -> True
    [UTF8.unit1|~|] -> True
    _ -> False

-------------------------------------------------------------------------------

identifier
  :: Position.Absolute
  -> Position.LineColumn
  -> State
  -> TokenList
identifier !startPosition !startLineColumn state@State {..}
  | position >= end =
      identifierToken input startPosition startLineColumn position Empty
  | otherwise = case index input position of
      [UTF8.unit1|.|] ->
        dotIdentifier startPosition startLineColumn position lineColumn $ incColumn 1 state
      c | Just n <- satisfy c isASCIIIdentifierCont Char.isAlpha state -> identifier startPosition startLineColumn $ incColumn n state
      _ ->
        identifierToken input startPosition startLineColumn position $
          lex state

dotIdentifier
  :: Position.Absolute
  -> Position.LineColumn
  -> Position.Absolute
  -> Position.LineColumn
  -> State
  -> TokenList
dotIdentifier !startPosition !startLineColumn !dotPosition !dotLineColumn state@State {..}
  | position >= end =
      identifierToken input startPosition startLineColumn dotPosition $
        Token dotLineColumn (Span.Absolute dotPosition position) Dot Empty
  | otherwise = case index input position of
      c
        | Just n <- satisfy c isASCIIIdentifierCont Char.isAlpha state -> identifier startPosition startLineColumn $ incColumn n state
        | Just n <- satisfy c isASCIIOperator (\c' -> Char.isSymbol c' || Char.isPunctuation c') state ->
            identifierToken input startPosition startLineColumn dotPosition $ operator dotPosition dotLineColumn $ incColumn n state
        | otherwise ->
            identifierToken input startPosition startLineColumn dotPosition $
              Token dotLineColumn (Span.Absolute dotPosition position) Dot $
                lex state

identifierToken
  :: Array
  -> Position.Absolute
  -> Position.LineColumn
  -> Position.Absolute
  -> TokenList
  -> TokenList
identifierToken !input !startPosition !startLineColumn !position =
  Token startLineColumn (Span.Absolute startPosition position) $
    case index input startPosition of
      [UTF8.unit1|_|] | len == 1 -> Underscore
      [UTF8.unit1|l|] | "let" <- str -> Let
      [UTF8.unit1|i|] | "in" <- str -> In
      [UTF8.unit1|d|] | "data" <- str -> Data
      [UTF8.unit1|w|] | "where" <- str -> Where
      [UTF8.unit1|f|] | "forall" <- str -> Forall
      [UTF8.unit1|c|] | "case" <- str -> Case
      [UTF8.unit1|o|] | "of" <- str -> Of
      _ -> Identifier str
  where
    len =
      position - startPosition

    str =
      Text.Text
        input
        (coerce startPosition)
        (coerce position - coerce startPosition)

-------------------------------------------------------------------------------

operator
  :: Position.Absolute
  -> Position.LineColumn
  -> State
  -> TokenList
operator !startPosition !startLineColumn state@State {..}
  | position >= end = operatorToken input startPosition startLineColumn position Empty
  | otherwise = case index input position of
      c
        | Just n <- satisfy c isASCIIOperator (\c' -> Char.isSymbol c' || Char.isPunctuation c') state ->
            operator startPosition startLineColumn $ incColumn n state
        | otherwise ->
            operatorToken input startPosition startLineColumn position $
              lex state

operatorToken
  :: Array
  -> Position.Absolute
  -> Position.LineColumn
  -> Position.Absolute
  -> TokenList
  -> TokenList
operatorToken !input !startPosition !startLineColumn !position =
  Token startLineColumn (Span.Absolute startPosition position) $
    case index input startPosition of
      [UTF8.unit1|=|] | len == 1 -> Equals
      [UTF8.unit1|.|] | len == 1 -> Dot
      [UTF8.unit1|:|] | len == 1 -> Colon
      [UTF8.unit1|||] | len == 1 -> Pipe
      [UTF8.unit1|-|] | "->" <- str -> RightArrow
      [UTF8.unit1|?|] | len == 1 -> QuestionMark
      [UTF8.unit1|~|] | len == 1 -> Forced
      _ -> Operator str
  where
    len =
      position - startPosition

    str =
      Text.Text
        input
        (coerce startPosition)
        (coerce position - coerce startPosition)

-------------------------------------------------------------------------------

number
  :: Position.Absolute
  -> Position.LineColumn
  -> State
  -> Bool
  -> Integer
  -> TokenList
number !startPosition !startLineColumn state@State {..} !shouldNegate !acc
  | position >= end =
      token Empty
  | otherwise =
      case index input position of
        c
          | isNumeric c -> do
              let acc' =
                    acc * 10 + fromIntegral (c - [UTF8.unit1|0|])
              number startPosition startLineColumn (incColumn 1 state) shouldNegate acc'
        _ ->
          token $ lex state
  where
    token =
      Token startLineColumn (Span.Absolute startPosition position) $
        Number $
          if shouldNegate then negate acc else acc

-------------------------------------------------------------------------------

singleLineComment :: State -> TokenList
singleLineComment state@State {..}
  | position >= end =
      Empty
  | otherwise =
      case index input position of
        [UTF8.unit1|
|] ->
            lex (incColumn 1 state) {lineColumn = Position.addLine lineColumn}
        _ ->
          singleLineComment $ incColumn 1 state

multiLineComment :: State -> Int -> TokenList
multiLineComment !state 0 =
  lex state
multiLineComment state@State {..} !depth
  | position >= end =
      Empty
  | otherwise =
      case index input position of
        [UTF8.unit1|{|]
          | position + 1 < end
          , [UTF8.unit1|-|] <- index input (position + 1) ->
              multiLineComment (incColumn 2 state) $ depth + 1
        [UTF8.unit1|-|]
          | position + 1 < end
          , [UTF8.unit1|}|] <- index input (position + 1) ->
              multiLineComment (incColumn 2 state) (depth - 1)
        [UTF8.unit1|
|] ->
            multiLineComment
              (incColumn 1 state)
                { lineColumn = Position.addLine lineColumn
                }
              depth
        _ ->
          multiLineComment (incColumn 1 state) depth

-- TODO: Fuzz tests for
--  length, line column
--  qualified identifiers
