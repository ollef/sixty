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

data TokenList
  = Empty
  | Token !State !Position.LineColumn !ByteString TokenList
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
      position' = position `plusAddr#` units
      tokenLength' = tokenLengthMultiplier state' * (tokenLength + I# units)
      newlineMultiplier_ = newlineMultiplier premultipliedClass
      !line' = line + newlineMultiplier_
      !column' = (column + I# units) * (1 - newlineMultiplier_)
    nextToken position' line' column' tokenLength' state'

{-# inline token #-}
token :: State -> ForeignPtr Word8 -> Addr# -> Int -> Int -> Int -> TokenList -> TokenList
token tok source@(ForeignPtr sourceAddress _) position length line column =
  Token tok (Position.LineColumn line (column - length)) (ByteString.PS source startPosition length)
  where
    endPosition =
      I# (position `minusAddr#` sourceAddress)
    startPosition =
      endPosition - length

toByteString :: ForeignPtr Word8 -> Addr# -> Int -> ByteString
toByteString source@(ForeignPtr sourceAddress _) endPosition length@(I# length_) =
  ByteString.PS source startPosition length
  where
    startPosition =
      I# (sourceAddress `minusAddr#` (endPosition `plusAddr#` negateInt# length_))

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
