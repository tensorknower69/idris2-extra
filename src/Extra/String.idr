module Extra.String

import Data.Fin
import Data.Nat
import Data.String
import Data.String.Extra
import Data.Vect
import Extra.Binary
import Extra.Fin
import Extra.Proof

-- TODO: I have no idea how should I be implementing this
public export
data NonEmpty : StrM xs -> Type where
  IsNonEmpty : {x : Char} -> {xs : String} -> NonEmpty (StrCons x xs)

export
Uninhabited (NonEmpty StrNil) where
  uninhabited IsNonEmpty impossible

export
hexLower : Fin 16 -> Char
hexLower 0 = '0'
hexLower 1 = '1'
hexLower 2 = '2'
hexLower 3 = '3'
hexLower 4 = '4'
hexLower 5 = '5'
hexLower 6 = '6'
hexLower 7 = '7'
hexLower 8 = '8'
hexLower 9 = '9'
hexLower 10 = 'a'
hexLower 11 = 'b'
hexLower 12 = 'c'
hexLower 13 = 'd'
hexLower 14 = 'e'
hexLower 15 = 'f'

export
hexUpper : Fin 16 -> Char
hexUpper = toUpper . hexLower

||| Turn a `Bits8` into a pair of bytes in `Fin` representation
private
bits8ToBytesFin : Bits8 -> (Fin 16, Fin 16)
bits8ToBytesFin x = divmodFinNZ (bits8ToFin x) 16 SIsNotZ

private
bits8ToHexChars : Bits8 -> (Char, Char)
bits8ToHexChars = bimap hexUpper hexUpper . bits8ToBytesFin

||| Turn a foldable of Bits8 into a upper hex string without '0x' prefix
export
hexString : Foldable f => f Bits8 -> String
hexString = foldr (\x, str => let (a, b) = bits8ToHexChars x in strCons a $ strCons b $ str) ""

export
asciiString : Foldable f => f Bits8 -> String
asciiString = foldr (\x, str => strCons (chr $ cast x) str) ""

||| Turn a string (NO UTF8) into a list of Bits8 by casting the ordinals of the chars of the string
export
unpackVect : (str : String) -> Vect (length str) Char
unpackVect str = case toVect (length str) (unpack str) of
  Nothing => crash "Extra.String.unpackVect: impossible case"
  Just t => t

