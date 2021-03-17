module Extra.Fin

import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.Nat.Division
import Extra.Binary
import Extra.Nat

export
bits8ToFin : Bits8 -> Fin 256
bits8ToFin n = helper 0
  where
  helper : Bits8 -> Fin 256
  helper m = believe_me $ if m == n then FZ else FS (helper (m + 1))

export
modFinNZ : Fin (S a) -> (b : Nat) -> Not (b = 0) -> Fin b
modFinNZ a b prf = let x = boundModNatNZ (finToNat a) b prf in natToFinLTE (modNatNZ (finToNat a) b prf) x

-- TODO: i have no idea how to prove this with the monotonic property of division or whatever its called by the true gameRZ of the community. For now i'm using natToFin, which is sacrilegious imo
export
divFinNZ : {a : Nat} -> Fin (S a) -> (b : Nat) -> (prf : Not (b = 0)) -> Fin (S (divNatNZ a b prf))
divFinNZ numer denom prf = case natToFin (divNatNZ (finToNat numer) denom prf) (S (divNatNZ a denom prf)) of
  Just x => x
  Nothing => last

export
divmodFinNZ : {a : Nat} -> Fin (S a) -> (b : Nat) -> (prf : Not (b = 0)) -> (Fin (S (divNatNZ a b prf)), Fin b)
divmodFinNZ a b prf = (divFinNZ a b prf, modFinNZ a b prf)
