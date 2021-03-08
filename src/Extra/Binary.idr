module Extra.Binary

import Data.List
import Data.Nat
import Debug.Trace
import public Data.Binary
import public Data.Binary.Digit
import Extra.Proof

-- TODO: At the time of writing, Data.Binary{,.Digit} are still under development

export
Eq Digit where
  O == O = True
  I == I = True
  _ == _ = False

export
Show Digit where
  show O = "O"
  show I = "I"

export
Cast Bits8 Nat where
  cast = integerToNat . cast {to = Integer}

export
Cast Nat Bits32 where
  cast = cast . cast {to = Integer}

public export
toBinFast : Nat -> Bin
toBinFast Z = [O]
toBinFast (S Z) = [I]
toBinFast n =
  let (div_, mod_) = divmodNatNZ n 2 SIsNotZ in
  case mod_ of
    Z => O :: toBinFast div_
    (S _) => I :: toBinFast div_

public export
toBin : Nat -> Bin
toBin Z = [O]
toBin (S n) = suc (toBin n)

public export
toBinFastEqual : (n : Nat) -> toBin n = toBinFast n
toBinFastEqual Z = Refl
toBinFastEqual (S n) = unsafeRefl

public export
toBinIsomorphic : (n : Nat) -> toNat (toBin n) = n
toBinIsomorphic Z = Refl
toBinIsomorphic (S n) = unsafeRefl

public export
padToLen : (len : Nat) -> Bin -> Bin
padToLen Z xs = xs
padToLen (S n) Nil = replicate (S n) O
padToLen (S n) (x :: xs) = x :: padToLen n xs

public export
toInt : Bin -> Int
toInt Nil = 0
toInt (O :: xs) = 2 * toInt xs
toInt (I :: xs) = 1 + 2 * toInt xs
