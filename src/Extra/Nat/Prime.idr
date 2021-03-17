||| Prime, coprime, compositie types for `Nat`
||| Extremely slow, but it totally works
||| No references, I just big brained lol
module Extra.Nat.Prime

import Data.Fin
import Data.Nat
import Data.Nat.Factor
import Data.Nat.Order
import Data.Nat.Order.Properties
import Decidable.Decidable

||| A witness of two numbers being relatively prime
public export
data Coprime : Nat -> Nat -> Type where
  MkCoprime : GCD 1 a b -> Coprime a b

||| A witness of two numbers not being relatively prime
public export
data NotCoprime : Nat -> Nat -> Type where
  MkNotCoprime0 : GCD 0 a b -> NotCoprime a b
  MkNotCoprime2 : GCD (S (S n)) a b -> NotCoprime a b

||| Coprimality of two `Nat`s
public export
data Coprimality : Nat -> Nat -> Type where
  TheyAreCoprime : Coprime a b -> Coprimality a b
  TheyArentCoprime : NotCoprime a b -> Coprimality a b

||| Calculate the coprimality of two `Nat`s
public export
coprimality : (a : Nat) -> (b : Nat) -> {auto ok: NotBothZero a b} -> Coprimality a b
coprimality a b with (Data.Nat.Factor.gcd a b)
  coprimality a b | (0 ** gcd_a_b) = TheyArentCoprime (MkNotCoprime0 gcd_a_b)
  coprimality a b | (1 ** gcd_a_b) = TheyAreCoprime (MkCoprime gcd_a_b)
  coprimality a b | ((S (S n)) ** gcd_a_b) = TheyArentCoprime (MkNotCoprime2 gcd_a_b)

||| Check are two numbers coprime to each other
public export
isCoprime : (a : Nat) -> (b : Nat) -> {auto ok: NotBothZero a b} -> Bool
isCoprime a b =
  case coprimality a b {ok = ok} of
   TheyAreCoprime _ => True
   _ => False

||| A witness of a `Nat` being a compositie number
public export
data Composite : Nat -> Type where
  MkComposite : (x : Nat) -> LTE 2 x -> LT x n -> Factor x n -> Composite n

||| A witness of a `Nat` being a prime number
public export
data Prime : Nat -> Type where
  MkPrime : ((x : Nat) -> LTE 2 x -> LT x n -> NotFactor x n) -> Prime n

||| Primality of a `Nat`
public export
data Primality : Nat -> Type where
  ItIsPrime : Prime n -> Primality n
  ItIsComposite : Composite n -> Primality n

||| This module's pseudo prime
public export
data PseudoPrime : Nat -> Nat -> Type where
  MkPseudoPrime : LTE 2 l -> LT l n -> ((x : Nat) -> LTE l x -> LT x n -> NotFactor x n) -> PseudoPrime l n

||| Constructs a trivial pseudo prime of a `Nat`
public export
trivial : (n : Nat) -> LTE 2 n -> PseudoPrime n (S n)
trivial 0 lte_2_n = void $ absurd lte_2_n
trivial 1 lte_2_n = void $ absurd lte_2_n
trivial (S (S n)) lte_2_n = MkPseudoPrime lte_2_n lteRefl lemma
  where
  gamma : (k : Nat) -> S k = plus (mult k 1) 1
  gamma k =
    rewrite multOneRightNeutral k in
    rewrite plusCommutative k 1 in
    Refl
  lemma : (x : Nat) -> LTE (S (S n)) x -> LTE (S x) (S (S (S n))) -> NotFactor x (S (S (S n)))
  lemma x lte lte' =
    let ccc = LTEIsAntisymmetric (S (S n)) x lte (fromLteSucc lte') in
    rewrite sym ccc in
    ProperRemExists 1 0 (gamma (S (S n)))

||| Realize the a `PseudoPrime` is an actual `Prime`
public export
realize : PseudoPrime 2 n -> Prime n
realize (MkPseudoPrime _ _ prf) = MkPrime prf

||| Strengthen a `PseudoPrime`, used to prove some other stuff
public export
strengthen : {l : Nat} -> LTE 2 l -> PseudoPrime (S l) n -> NotFactor l n -> PseudoPrime l n
strengthen lte (MkPseudoPrime _ lt_l_n prf) notfactor_l_n = MkPseudoPrime lte (lteSuccLeft lt_l_n) lemma
  where
  lemma : (x : Nat) -> LTE l x -> LT x n -> NotFactor x n
  lemma x lte_l_x lt_x_n = case isLTE (S l) x of
    Yes lte_Sl_x => prf x lte_Sl_x lt_x_n
    No contra => rewrite (LTEIsAntisymmetric x l (fromLteSucc $ notlteIsLT (S l) x $ notLteIsnotlte (S l) x contra) lte_l_x) in notfactor_l_n

||| The prime number 2, proved manually
public export
prime2 : Prime 2
prime2 = MkPrime lemma
  where
  lemma : (x : Nat) -> LTE 2 x -> LT x 2 -> NotFactor x 2
  lemma 0 lte_2_0 _ = void $ absurd lte_2_0
  lemma 1 lte_2_1 _ = void $ absurd lte_2_1
  lemma (S (S n)) _ lt_2_n = void $ absurd lt_2_n

||| Calculates a `Nat`'s primality
public export
primality : (n : Nat) -> LTE 2 n -> Primality n
primality 0 lte_2_0 = void $ absurd lte_2_0
primality 1 lte_2_1 = void $ absurd lte_2_1
primality 2 lte_2_2 = ItIsPrime prime2
primality n@(S (S (S k))) lte_2_n = lemma (trivial (S (S k)) (LTESucc $ LTESucc $ LTEZero))
  where
  lemma : {x : Nat} -> PseudoPrime (S (S x)) (S (S (S k))) -> Primality (S (S (S k)))
  lemma {x = 0} p = ItIsPrime (realize p)
  lemma {x = (S y)} p@(MkPseudoPrime lte_2_x lte_x_n prf) =
    case decFactor (S (S (S k))) (S (S y)) of
      ItIsFactor factor => ItIsComposite $ MkComposite (S (S y)) (lteAddRight {m = y} 2) (lteSuccLeft lte_x_n) factor
      ItIsNotFactor not_factor => lemma (strengthen (lteAddRight {m = y} 2) p not_factor)

||| Check if a `Nat` is a prime number
public export
isPrime : (n : Nat) -> {auto okay : LTE 2 n} -> Bool
isPrime 1 = void $ absurd okay
isPrime (S (S n)) = case primality (S (S n)) okay of
  ItIsPrime _ => True
  ItIsComposite _ => False
