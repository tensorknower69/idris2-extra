module Extra.String

import Data.Fin
import Data.Nat
import Data.String
import Extra.Binary
import Data.String.Extra
import Extra.Fin

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

||| Turns a `Bits8` into a pair of bytes in `Fin` representation
private
bits8ToBytesFin : Bits8 -> (Fin 16, Fin 16)
bits8ToBytesFin x = divmodFinNZ (bits8ToFin x) 16 SIsNotZ

export
bits8ToHexChars : Bits8 -> (Char, Char)
bits8ToHexChars = bimap hexUpper hexUpper . bits8ToBytesFin

export
hexString : Foldable f => f Bits8 -> String
hexString = foldr (\x, str => let (a, b) = bits8ToHexChars x in strCons a $ strCons b $ str) ""
