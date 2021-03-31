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
{-# language UnboxedTuples #-}
module Lexer2 where

import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Internal as ByteString
import GHC.Exts
import GHC.ForeignPtr (ForeignPtr(..))
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
lex !source = do
  go 0 0 0 InitialState
  where
    go !tokenLength !line !column !state !position = do
      let
        !(# premultipliedClass, units #) = classify position
        state' = nextState $ premultipliedClassState premultipliedClass state
      if state' <= LastDone then
        case state' of
          EndOfFileDone -> Empty
          IdentifierDotDone -> identifierDot source position tokenLength line column $ go 0 line column InitialState position
          _ -> token state' source position tokenLength line column $ go 0 line column InitialState position
      else do
        let
          position' = position `plusAddr#` units
          tokenLength' = tokenLengthMultiplier state' * (tokenLength + I# units)
          newlineMultiplier_ = newlineMultiplier premultipliedClass
          line' = line + newlineMultiplier_
          column' = (column + I# units) * (1 - newlineMultiplier_)
        go tokenLength' line' column' state' position'

{-# inline token #-}
token :: State -> ForeignPtr Word8 -> Addr# -> Int -> Int -> Int -> TokenList -> TokenList
token tok source@(ForeignPtr sourceAddress _) position length line column =
  Token
    tok
    (Position.LineColumn line (column - length))
    (ByteString.PS source startPosition length)
  where
    endPosition =
      I# (position `minusAddr#` sourceAddress)
    startPosition =
      endPosition - length

{-# inline identifierDot #-}
identifierDot :: ForeignPtr Word8 -> Addr# -> Int -> Int -> Int -> TokenList -> TokenList
identifierDot source position length line column =
  token IdentifierDone source (position `plusAddr#` -1#) (length - 1) line (column - 1) .
  token OperatorDone source position 1 line column

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
