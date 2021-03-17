module Extra.Binary

import public Data.Binary.Digit
import Data.Bits
import Data.DPair
import Data.Vect
import Data.Nat

||| `False` -> `O`, `True` -> `I`
public export
boolToDigit : Bool -> Digit
boolToDigit False = O
boolToDigit True = I

||| `O` -> `0`, `I` -> `1`
export
digitToInteger : Digit -> Integer
digitToInteger O = 0
digitToInteger I = 1

||| A type to represent endianness
public export
data Endianness : Type where
  ||| Little endian
  LE : Endianness
  ||| Big endian
  BE : Endianness

||| `LE` -> `BE`, `BE` -> `LE`
public export
flip : Endianness -> Endianness
flip LE = BE
flip BE = LE

||| Binary representation, basically `Vect` but takes account into endianness
public export
data Binary : Endianness -> Nat -> Type where
  Nil : Binary endian 0
  (::) : Digit -> Binary endian n -> Binary endian (S n)

||| Convert a `Vect` into a `Binary LE`
public export
fromVectLE : Vect n Digit -> Binary LE n
fromVectLE Nil = Nil
fromVectLE (x :: xs) = x :: fromVectLE xs

||| Convert a `Vect` into a `Binary BE`
public export
fromVectBE : Vect n Digit -> Binary BE n
fromVectBE Nil = Nil
fromVectBE (x :: xs) = x :: fromVectBE xs

||| An auxiliary function for `reverse`, useful for proving stuff
public export
reverseOnto : Binary (flip endian) a -> Binary endian m -> Binary (flip endian) (a + m)
reverseOnto acc Nil = rewrite plusZeroRightNeutral a in acc
reverseOnto {m = S n} acc (x :: xs) = rewrite sym (plusSuccRightSucc a n) in reverseOnto (x :: acc) xs

||| Reverse a `Binary`, and flips its endianness
public export
reverse : Binary endian n -> Binary (flip endian) n
reverse xs = reverseOnto Nil xs

||| Some helper function for showing `Binary BE`
private
showBEHelper : {default True first : Bool} -> Binary BE n -> String
showBEHelper {first = False} Nil = ""
showBEHelper {first = False} (O :: xs) = strCons '0' (showBEHelper {first = False} xs)
showBEHelper {first = False} (I :: xs) = strCons '1' (showBEHelper {first = False} xs)
showBEHelper {first = True} xs = "0b" <+> showBEHelper {first = False} xs

export
{endian : Endianness} -> Show (Binary endian n) where
  show Nil = ""
  show {endian = LE} xs = show $ reverse xs
  show {endian = BE} xs = showBEHelper xs

||| Converts a `Bits8` into `Binary LE 8`
export
fromBits8LE : Bits8 -> Binary LE 8
fromBits8LE m = fromVectLE $ map (boolToDigit . testBit m)
  [ (Element 0 (lteReflectsLTE 1 8 Refl))
  , (Element 1 (lteReflectsLTE 2 8 Refl))
  , (Element 2 (lteReflectsLTE 3 8 Refl))
  , (Element 3 (lteReflectsLTE 4 8 Refl))
  , (Element 4 (lteReflectsLTE 5 8 Refl))
  , (Element 5 (lteReflectsLTE 6 8 Refl))
  , (Element 6 (lteReflectsLTE 7 8 Refl))
  , (Element 7 (lteReflectsLTE 8 8 Refl))
  ]

||| Converts a `Bits16` into `Binary LE 16`
export
fromBits16LE : Bits16 -> Binary LE 16
fromBits16LE m = fromVectLE $ map (boolToDigit . testBit m)
  [ Element 0 (lteReflectsLTE 1 16 Refl)
  , Element 1 (lteReflectsLTE 2 16 Refl)
  , Element 2 (lteReflectsLTE 3 16 Refl)
  , Element 3 (lteReflectsLTE 4 16 Refl)
  , Element 4 (lteReflectsLTE 5 16 Refl)
  , Element 5 (lteReflectsLTE 6 16 Refl)
  , Element 6 (lteReflectsLTE 7 16 Refl)
  , Element 7 (lteReflectsLTE 8 16 Refl)
  , Element 8 (lteReflectsLTE 9 16 Refl)
  , Element 9 (lteReflectsLTE 10 16 Refl)
  , Element 10 (lteReflectsLTE 11 16 Refl)
  , Element 11 (lteReflectsLTE 12 16 Refl)
  , Element 12 (lteReflectsLTE 13 16 Refl)
  , Element 13 (lteReflectsLTE 14 16 Refl)
  , Element 14 (lteReflectsLTE 15 16 Refl)
  , Element 15 (lteReflectsLTE 16 16 Refl)
  ]

||| Converts a `Bits32` into `Binary LE 32`
export
fromBits32LE : Bits32 -> Binary LE 32
fromBits32LE m = fromVectLE $ map (boolToDigit . testBit m)
  [ Element 0 (lteReflectsLTE 1 32 Refl)
  , Element 1 (lteReflectsLTE 2 32 Refl)
  , Element 2 (lteReflectsLTE 3 32 Refl)
  , Element 3 (lteReflectsLTE 4 32 Refl)
  , Element 4 (lteReflectsLTE 5 32 Refl)
  , Element 5 (lteReflectsLTE 6 32 Refl)
  , Element 6 (lteReflectsLTE 7 32 Refl)
  , Element 7 (lteReflectsLTE 8 32 Refl)
  , Element 8 (lteReflectsLTE 9 32 Refl)
  , Element 9 (lteReflectsLTE 10 32 Refl)
  , Element 10 (lteReflectsLTE 11 32 Refl)
  , Element 11 (lteReflectsLTE 12 32 Refl)
  , Element 12 (lteReflectsLTE 13 32 Refl)
  , Element 13 (lteReflectsLTE 14 32 Refl)
  , Element 14 (lteReflectsLTE 15 32 Refl)
  , Element 15 (lteReflectsLTE 16 32 Refl)
  , Element 16 (lteReflectsLTE 17 32 Refl)
  , Element 17 (lteReflectsLTE 18 32 Refl)
  , Element 18 (lteReflectsLTE 19 32 Refl)
  , Element 19 (lteReflectsLTE 20 32 Refl)
  , Element 20 (lteReflectsLTE 21 32 Refl)
  , Element 21 (lteReflectsLTE 22 32 Refl)
  , Element 22 (lteReflectsLTE 23 32 Refl)
  , Element 23 (lteReflectsLTE 24 32 Refl)
  , Element 24 (lteReflectsLTE 25 32 Refl)
  , Element 25 (lteReflectsLTE 26 32 Refl)
  , Element 26 (lteReflectsLTE 27 32 Refl)
  , Element 27 (lteReflectsLTE 28 32 Refl)
  , Element 28 (lteReflectsLTE 29 32 Refl)
  , Element 29 (lteReflectsLTE 30 32 Refl)
  , Element 30 (lteReflectsLTE 31 32 Refl)
  , Element 31 (lteReflectsLTE 32 32 Refl)
  ]

||| Convert a `Binary` into its corresponding integer representation
export
toInteger : {endian : Endianness} -> Binary endian n -> Integer
toInteger Nil = 0
toInteger {endian = LE} (x :: xs) = digitToInteger x + 2 * (toInteger xs)
toInteger {endian = BE} xs = toInteger $ reverse xs

public export
append : Binary endian m -> Binary endian n -> Binary endian (m + n)
append Nil ys = ys
append (x :: xs) ys = x :: (append xs ys)
