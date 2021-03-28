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
import qualified Data.Char as Char
import qualified Data.Vector.Unboxed as Vector
import GHC.Exts
import GHC.ForeignPtr (ForeignPtr(..))
import qualified Position
import Protolude hiding (State, state, length)
import qualified Span
import UTF8
import Lexer2.State
import Lexer2.Class
import Lexer2.Tables

data TokenList
  = Empty
  | Token !Position.LineColumn !Span.Absolute !Token !TokenList
  deriving (Show, Generic, NFData)

data Token
  -- Identifiers
  = Identifier !ByteString
  -- Reserved identifiers
  | Let
  | In
  | Data
  | Where
  | Forall
  | Case
  | Of
  | Underscore
  -- Operators
  | Operator !ByteString
  -- Reserved operators
  | Equals
  | Dot
  | Colon
  | Pipe
  | RightArrow
  | QuestionMark
  | Forced
  -- Special
  | Number !Integer
  | Lambda
  | LeftParen
  | RightParen
  | LeftImplicitBrace
  | RightImplicitBrace
  | Error
  deriving (Eq, Show, Generic, NFData)

lexByteString :: ByteString -> TokenList
lexByteString bs =
  lexNullTerminatedByteString $ bs <> "\0"

lexNullTerminatedByteString :: ByteString -> TokenList
lexNullTerminatedByteString (ByteString.PS source@(ForeignPtr sourceAddress _) (I# offset) _) =
  lex source (sourceAddress `plusAddr#` offset) 0 0 0 InitialState

lex :: ForeignPtr Word8 -> Addr# -> Int -> Int -> Int -> State -> TokenList
lex !source !position !tokenLength !line !column !state = do
  let
    !(# premultipliedClass, units #) = classify position
    state' = nextState $ premultipliedClassState premultipliedClass state
  if state' < FirstDone then do
    let
      position' = position `plusAddr#` units
      tokenLength' = tokenLengthMultiplier state' * (tokenLength + I# units)
      newlineMultiplier_ = newlineMultiplier premultipliedClass
      line' = line + newlineMultiplier_
      column' = (column + I# units) * (1 - newlineMultiplier_)
    lex source position' tokenLength' line' column' state'
  else
    case state' of
      NumberDone -> token number source position tokenLength line column $ lex source position 0 line column InitialState
      IdentifierDone -> token Identifier source position tokenLength line column $ lex source position 0 line column InitialState
      IdentifierDotDone -> identifierDot source position tokenLength line column $ lex source position 0 line column InitialState
      OperatorDone -> token Operator source position tokenLength line column $ lex source position 0 line column InitialState
      LeftParenDone -> token_ LeftParen source position tokenLength line column $ lex source position 0 line column InitialState
      RightParenDone -> token_ RightParen source position tokenLength line column $ lex source position 0 line column InitialState
      ErrorDone -> token_ Error source position tokenLength line column $ lex source position 0 line column InitialState
      EndOfFileDone -> Empty
      _ -> panic "lex non-done done state"

{-# inline token #-}
token :: (ByteString -> Token) -> ForeignPtr Word8 -> Addr# -> Int -> Int -> Int -> TokenList -> TokenList
token makeToken source@(ForeignPtr sourceAddress _) position length line column =
  Token
    (Position.LineColumn line (column - length))
    (Span.Absolute (Position.Absolute startPosition) (Position.Absolute endPosition))
    (makeToken $ ByteString.PS source startPosition length)
  where
    endPosition =
      I# (position `minusAddr#` sourceAddress)
    startPosition =
      endPosition - length

{-# inline token_ #-}
token_ :: Token -> ForeignPtr Word8 -> Addr# -> Int -> Int -> Int -> TokenList -> TokenList
token_ makeToken (ForeignPtr sourceAddress _) position length line column =
  Token
    (Position.LineColumn line (column - length))
    (Span.Absolute (Position.Absolute startPosition) (Position.Absolute endPosition))
    makeToken
  where
    endPosition =
      I# (position `minusAddr#` sourceAddress)
    startPosition =
      endPosition - length

number :: ByteString -> Token
number =
  Number . go 0
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

{-# inline identifierDot #-}
identifierDot :: ForeignPtr Word8 -> Addr# -> Int -> Int -> Int -> TokenList -> TokenList
identifierDot source position length line column =
  token Identifier source (position `plusAddr#` -1#) (length - 1) line (column - 1) .
  token_ Dot source position 1 line column

toByteString :: ForeignPtr Word8 -> Addr# -> Int -> ByteString
toByteString source@(ForeignPtr sourceAddress _) endPosition length@(I# length_) =
  ByteString.PS source startPosition length
  where
    startPosition =
      I# (sourceAddress `minusAddr#` (endPosition `plusAddr#` negateInt# length_))

tokenLengthMultiplier :: State -> Int
tokenLengthMultiplier s =
  tokenLengthMultiplierTable `Vector.unsafeIndex` fromIntegral (unstate s)

newlineMultiplier :: PremultipliedClass -> Int
newlineMultiplier c =
  newlineMultiplierTable `Vector.unsafeIndex` fromIntegral (unpremultipliedClass c)

{-# inline nextState #-}
nextState :: PremultipliedClassState -> State
nextState (PremultipliedClassState cs) =
  State $ nextStateTable `Vector.unsafeIndex` fromIntegral cs

{-# inline classify #-}
classify :: Addr# -> (# PremultipliedClass, Int# #)
classify position = do
  let
    c1 = indexCharOffAddr# position 0#
  if UTF8.validate1 c1 then
    (# classify1 c1, 1# #)
  else do
    let
      c2 = indexCharOffAddr# position 1#
    if UTF8.validate2 c1 then
      (# classifyChar $ UTF8.chr2 c1 c2, 2# #)
    else do
      let
        c3 = indexCharOffAddr# position 2#
      if UTF8.validate3 c1 then
        (# classifyChar $ UTF8.chr3 c1 c2 c3, 3# #)
      else do
        let
          c4 = indexCharOffAddr# position 3#
        (# classifyChar $ UTF8.chr4 c1 c2 c3 c4, 4# #)

{-# inline classify1 #-}
classify1 :: Char# -> PremultipliedClass
classify1 c = PremultipliedClass $ classify1Table `Vector.unsafeIndex` ord (C# c)

{-# inline classifyChar #-}
classifyChar :: Char -> PremultipliedClass
classifyChar c
  | Char.isAlphaNum c = premultiply AlphaClass
  | Char.isSymbol c = premultiply OperatorClass
  | Char.isPunctuation c = premultiply OperatorClass
  | otherwise = premultiply ErrorClass
