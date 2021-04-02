{-# language BangPatterns #-}
{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language PatternSynonyms #-}
{-# language UnboxedTuples #-}
{-# language UnliftedNewtypes #-}
{-# language ViewPatterns #-}
module Lexer2 where

import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Internal as ByteString
import GHC.Exts
import GHC.ForeignPtr (ForeignPtr(..))
import GHC.Word
import Lexer2.Classification
import Lexer2.State
import Lexer2.Transition
import qualified Position
import Protolude hiding (State, state, length)
import qualified Span

newtype InnerToken = InnerToken Word8
  deriving (Eq, Show, Generic)
  deriving newtype NFData
  -- Identifiers
pattern Identifier = InnerToken 0
pattern Let = InnerToken 1
pattern In = InnerToken 2
pattern Data = InnerToken 3
pattern Where = InnerToken 4
pattern Forall = InnerToken 5
pattern Case = InnerToken 6
pattern Of = InnerToken 7
pattern Underscore = InnerToken 8
pattern Operator = InnerToken 9
pattern Equals = InnerToken 10
pattern Dot = InnerToken 11
pattern Colon = InnerToken 12
pattern Pipe = InnerToken 13
pattern RightArrow = InnerToken 14
pattern QuestionMark = InnerToken 15
pattern Forced = InnerToken 16
pattern Number = InnerToken 17
pattern Lambda = InnerToken 18
pattern LeftParen = InnerToken 19
pattern RightParen = InnerToken 20
pattern LeftImplicitBrace = InnerToken 21
pattern RightImplicitBrace = InnerToken 22
pattern Error = InnerToken 23

{-# inline toToken #-}
toToken :: ForeignPtr Word8 -> State -> Span.Absolute -> InnerToken
toToken source state (Span.Absolute (Position.Absolute startPosition) (Position.Absolute endPosition)) =
  case state of
    IdentifierDone ->
      case ByteString.PS source startPosition (endPosition - startPosition) of
        "let" -> Let
        "in" -> In
        "data" -> Data
        "where" -> Where
        "forall" -> Forall
        "case" -> Case
        "of" -> Of
        "_" -> Underscore
        _ -> Identifier
    OperatorDone ->
      case ByteString.PS source startPosition (endPosition - startPosition) of
        "=" -> Equals
        "." -> Dot
        ":" -> Colon
        "|" -> Pipe
        "->" -> RightArrow
        "?" -> QuestionMark
        "~" -> Forced
        "\\" -> Lambda
        _ -> Operator
    NumberDone -> Number
    LeftParenDone -> LeftParen
    RightParenDone -> RightParen
    LeftImplicitBraceDone -> LeftImplicitBrace
    RightImplicitBraceDone -> RightImplicitBrace
    ErrorDone -> Error
    _ -> panic $ "toToken: " <> show state

displayToken :: InnerToken -> ByteString -> Text
displayToken token_ bs =
  case token_ of
    Identifier -> decodeUtf8 bs
    Let -> "let"
    In -> "in"
    Data -> "data"
    Where -> "where"
    Forall -> "forall"
    Case -> "case"
    Of -> "of"
    Underscore -> "_"

    Operator -> decodeUtf8 bs
    Equals -> "="
    Dot -> "."
    Colon -> ":"
    Pipe -> "|"
    RightArrow -> "->"
    QuestionMark -> "?"
    Forced -> "~"

    Number -> decodeUtf8 bs
    Lambda -> "\\"
    LeftParen -> "("
    RightParen -> ")"
    LeftImplicitBrace -> "@{"
    RightImplicitBrace -> "}"
    Error -> "[error]"
    _ -> panic "No such token"

data TokenList
  = Empty
  | Token !InnerToken !Position.LineColumn !Span.Absolute TokenList
  deriving (Show, Generic, NFData)

tokenSpan :: ByteString -> Span.Absolute
tokenSpan (ByteString.PS _ offset length) =
  Span.Absolute (Position.Absolute offset) (Position.Absolute $ offset + length)

lexByteString :: ByteString -> TokenList
lexByteString bs
  | ByteString.length bs > 0 && ByteString.last bs == 0 = lexNullTerminatedByteString bs
  | otherwise = lexNullTerminatedByteString $ bs <> "\0"

lexNullTerminatedByteString :: ByteString -> TokenList
lexNullTerminatedByteString (ByteString.PS source@(ForeignPtr sourceAddress _) 0 _) = lex source sourceAddress
lexNullTerminatedByteString bs@(ByteString.PS _ (I# _offset) _) = lexNullTerminatedByteString $ ByteString.copy bs

lex :: ForeignPtr Word8 -> Addr# -> TokenList
lex !source !startPosition = go startPosition 0 0
  where
    go !position !line !column = do
      let
        !(Lexer position' line' column' tokenLength' state') = nextToken position line column 0 InitialState
      case state' of
        EndOfFileDone -> Empty
        _ -> token state' source position' tokenLength' line' column' $ go position' line' column'

type Lexer = (# Addr#, Int#, Int#, Int#, Word# #)

pattern Lexer :: Addr# -> Int -> Int -> Int -> State -> Lexer
pattern Lexer position line column tokenLength state <- (# position, I# -> line, I# -> column, I# -> tokenLength, \s -> State (W8# s) -> state #)
  where
    Lexer position (I# line) (I# column) (I# tokenLength) (State (W8# state)) =
      (# position, line, column, tokenLength, state #)

{-# complete Lexer #-}

nextToken :: Addr# -> Int -> Int -> Int -> State -> Lexer
nextToken !position !line !column !tokenLength !state = do
  let
    !(# premultipliedClass, units #) = classify position
    !state' = nextState $ premultipliedClassState premultipliedClass state
  if state' >= FirstDone then do
    let
      offset = doneFromOffset state
      position' = position `plusAddr#` offset
      column' = column + I# offset
      tokenLength' = tokenLength + I# offset
    Lexer position' line column' tokenLength' state'
  else do
    let
      !position' = position `plusAddr#` units
      !tokenLength' = tokenLengthMultiplier state' * (tokenLength + I# units)
      !newlineMultiplier_ = newlineMultiplier premultipliedClass
      !line' = line + newlineMultiplier_
      !column' = (column + I# units) * (1 - newlineMultiplier_)
    nextToken position' line' column' tokenLength' state'

{-# inline token #-}
token :: State -> ForeignPtr Word8 -> Addr# -> Int -> Int -> Int -> TokenList -> TokenList
token st source@(ForeignPtr sourceAddress _) position length line column =
  Token (toToken source st span) (Position.LineColumn line (column - length)) (Span.Absolute (Position.Absolute startPosition) (Position.Absolute endPosition))
  where
    endPosition =
      I# (position `minusAddr#` sourceAddress)
    startPosition =
      endPosition - length
    span =
      Span.Absolute (Position.Absolute startPosition) (Position.Absolute endPosition)

toByteString :: ForeignPtr Word8 -> Span.Absolute -> ByteString
toByteString source (Span.Absolute (Position.Absolute startPosition) (Position.Absolute endPosition)) =
  ByteString.PS source startPosition length
  where
    !length = endPosition - startPosition

parseNumber :: ByteString -> Integer
parseNumber =
  go 0
  where
    go :: Integer -> ByteString -> Integer
    go !acc bs =
      case ByteString.uncons bs of
        Nothing ->
          acc

        Just (b, bs')
          | b == fromIntegral (ord '-') ->
            negate $ go 0 bs'

          | otherwise ->
            go (acc * 10 + fromIntegral b - fromIntegral (ord '0')) bs'
