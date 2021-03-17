module Extra.Nat

import Data.Fin
import Data.Nat
import Data.Nat.Equational
import Data.Nat.Division

public export
subtract : (n : Nat) -> Fin (S n) -> Nat
subtract n FZ = n
subtract (S n) (FS k) = subtract n k

export
lteAsymRefl : {a, b : Nat} -> a = b -> LTE a b
lteAsymRefl Refl = lteRefl

export
divNatNZLteNumer : (numer : Nat) -> (denom : Nat) -> (prf : Not (denom = 0)) -> LTE (divNatNZ numer denom prf) numer
divNatNZLteNumer a Z prf = void $ prf Refl
divNatNZLteNumer a (S b) prf =
  let lte1 = lteAddRight {m = (snd (divmodNatNZ a (S b) prf))} (mult (fst (divmodNatNZ a (S b) prf)) (S b)) in
  let a1 = lteAsymRefl $ sym (DivisionTheoremDivMod a (S b) prf) in
  let a2 = lteTransitive lte1 (rewrite plusCommutative (mult (fst (divmodNatNZ a (S b) prf)) (S b)) (snd (divmodNatNZ a (S b) prf)) in a1) in
  let lte2 = leftFactorLteProduct (fst (divmodNatNZ a (S b) prf)) b in
  let a3 = lteTransitive lte2 a2 in
  rewrite sym $ fstDivmodNatNZeqDiv a (S b) prf prf in a3
