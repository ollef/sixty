{-# language PatternSynonyms #-}
{-# language GeneralizedNewtypeDeriving #-}
module Lexer2.State where

import Data.Word
import Protolude hiding (State)

newtype State = State { unstate :: Word8 }
  deriving (Eq, Ord, Show)

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
pattern LeftBraceState :: State
pattern LeftBraceState = State 7
pattern RightBraceState :: State
pattern RightBraceState = State 8
pattern OperatorState :: State
pattern OperatorState = State 9
pattern SingleLineCommentState :: State
pattern SingleLineCommentState = State 10
pattern MultiLineCommentState :: State
pattern MultiLineCommentState = State 11
pattern MultiLineCommentMinusState :: State
pattern MultiLineCommentMinusState = State 12
pattern ErrorState :: State
pattern ErrorState = State 13
pattern StateCount :: State
pattern StateCount = FirstDone

pattern FirstDone :: State
pattern FirstDone = NumberDone
pattern NumberDone :: State
pattern NumberDone = State 14
pattern IdentifierDone :: State
pattern IdentifierDone = State 15
pattern IdentifierDotDone :: State
pattern IdentifierDotDone = State 16
pattern OperatorDone :: State
pattern OperatorDone = State 17
pattern LeftParenDone :: State
pattern LeftParenDone = State 18
pattern RightParenDone :: State
pattern RightParenDone = State 19
pattern ErrorDone :: State
pattern ErrorDone = State 20
pattern EndOfFileDone :: State
pattern EndOfFileDone = State 21
