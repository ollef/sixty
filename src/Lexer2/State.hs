{-# language PatternSynonyms #-}
{-# language GeneralizedNewtypeDeriving #-}
module Lexer2.State where

import Data.Word
import Protolude hiding (State)

newtype Class = Class { classToWord8 :: Word8 }
  deriving Show

newtype PremultipliedClass = PremultipliedClass { premultipliedClassToWord16 :: Word16 }
  deriving Eq

{-# inline premultiply #-}
premultiply :: Class -> PremultipliedClass
premultiply (Class c) = PremultipliedClass $ fromIntegral (stateToWord8 StateCount) * fromIntegral c

{-# inline unpremultiply #-}
unpremultiply :: PremultipliedClass -> Class
unpremultiply (PremultipliedClass p) =
  Class $ fromIntegral $ p `div` fromIntegral (stateToWord8 StateCount)

newtype PremultipliedClassState = PremultipliedClassState Word16

{-# inline premultipliedClassState #-}
premultipliedClassState :: PremultipliedClass -> State -> PremultipliedClassState
premultipliedClassState (PremultipliedClass c) (State s) = PremultipliedClassState $ c + fromIntegral s

{-# inline unpremultiplyClassState #-}
unpremultiplyClassState :: PremultipliedClassState -> (Class, State)
unpremultiplyClassState (PremultipliedClassState cs) =
  bimap (Class . fromIntegral) (State . fromIntegral) $ quotRem cs $ fromIntegral $ stateToWord8 StateCount

newtype State = State { stateToWord8 :: Word8 }
  deriving (Eq, Ord, Show, NFData)

pattern WhitespaceClass :: Class
pattern WhitespaceClass = Class 0
pattern NewlineClass :: Class
pattern NewlineClass = Class 1
pattern AlphaClass :: Class
pattern AlphaClass = Class 2
pattern NumericClass :: Class
pattern NumericClass = Class 3
pattern LeftParenClass :: Class
pattern LeftParenClass = Class 4
pattern RightParenClass :: Class
pattern RightParenClass = Class 5
pattern DotClass :: Class
pattern DotClass = Class 6
pattern PrimeClass :: Class
pattern PrimeClass = Class 7
pattern MinusClass :: Class
pattern MinusClass = Class 8
pattern OperatorClass :: Class
pattern OperatorClass = Class 9
pattern AtClass :: Class
pattern AtClass = Class 10
pattern LeftBraceClass :: Class
pattern LeftBraceClass = Class 11
pattern RightBraceClass :: Class
pattern RightBraceClass = Class 12
pattern EndOfFileClass :: Class
pattern EndOfFileClass = Class 13
pattern ErrorClass :: Class
pattern ErrorClass = Class 14
pattern ClassCount :: Class
pattern ClassCount = Class 15

pattern InitialState :: State
pattern InitialState = State 0
pattern IdentifierState :: State
pattern IdentifierState = State 1
pattern IdentifierDotState :: State
pattern IdentifierDotState = State 2
pattern NumberState :: State
pattern NumberState = State 3
pattern MinusState :: State
pattern MinusState = State 4
pattern LeftParenState :: State
pattern LeftParenState = State 5
pattern RightParenState :: State
pattern RightParenState = State 6
pattern AtState :: State
pattern AtState = State 7
pattern LeftBraceState :: State
pattern LeftBraceState = State 8
pattern RightBraceState :: State
pattern RightBraceState = State 9
pattern OperatorState :: State
pattern OperatorState = State 10
pattern SingleLineCommentState :: State
pattern SingleLineCommentState = State 11
pattern MultiLineCommentState :: State
pattern MultiLineCommentState = State 12
pattern MultiLineCommentMinusState :: State
pattern MultiLineCommentMinusState = State 13
pattern ErrorState :: State
pattern ErrorState = State 14
pattern StateCount :: State
pattern StateCount = State 15

pattern FirstDone :: State
pattern FirstDone = NumberDone

pattern NumberDone :: State
pattern NumberDone = State 16
pattern IdentifierDone :: State
pattern IdentifierDone = State 17
pattern OperatorDone :: State
pattern OperatorDone = State 18
pattern LeftParenDone :: State
pattern LeftParenDone = State 19
pattern RightParenDone :: State
pattern RightParenDone = State 20
pattern LeftImplicitBraceDone :: State
pattern LeftImplicitBraceDone = State 21
pattern RightImplicitBraceDone :: State
pattern RightImplicitBraceDone = State 22
pattern ErrorDone :: State
pattern ErrorDone = State 23
pattern EndOfFileDone :: State
pattern EndOfFileDone = State 24
