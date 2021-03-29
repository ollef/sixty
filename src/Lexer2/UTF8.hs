{-# language MagicHash #-}
module Lexer2.UTF8 where

import GHC.Exts
import Protolude

{-# inline validate1 #-}
validate1 :: Char# -> Bool
validate1 x1 =
  isTrue# (x1 `leChar#` '\x7F'#) 

{-# inline validate2 #-}
validate2 :: Char# -> Bool
validate2 x1 =
  isTrue# (x1 `leChar#` '\xDF'#)

{-# inline validate3 #-}
validate3 :: Char# -> Bool
validate3 x1 =
  isTrue# (x1 `leChar#` '\xEF'#)

{-# inline chr2 #-}
chr2 :: Char# -> Char# -> Char
chr2 x1 x2 =
  C# (chr# (z1 +# z2))
  where
    y1 = ord# x1
    y2 = ord# x2
    z1 = uncheckedIShiftL# (y1 -# 0xC0#) 6#
    z2 = y2 -# 0x80#

{-# inline chr3 #-}
chr3 :: Char# -> Char# -> Char# -> Char
chr3 x1 x2 x3 =
  C# (chr# (z1 +# z2 +# z3))
  where
    y1 = ord# x1
    y2 = ord# x2
    y3 = ord# x3
    z1 = uncheckedIShiftL# (y1 -# 0xE0#) 12#
    z2 = uncheckedIShiftL# (y2 -# 0x80#) 6#
    z3 = y3 -# 0x80#

{-# inline chr4 #-}
chr4 :: Char# -> Char# -> Char# -> Char# -> Char
chr4 x1 x2 x3 x4 =
  C# (chr# (z1 +# z2 +# z3 +# z4))
  where
    y1 = ord# x1
    y2 = ord# x2
    y3 = ord# x3
    y4 = ord# x4
    z1 = uncheckedIShiftL# (y1 -# 0xF0#) 18#
    z2 = uncheckedIShiftL# (y2 -# 0x80#) 12#
    z3 = uncheckedIShiftL# (y3 -# 0x80#) 6#
    z4 = y4 -# 0x80#
