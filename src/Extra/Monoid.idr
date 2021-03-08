module Extra.Monoid

import Data.List
import Data.List1

public export
merge : Monoid m => (m, m) -> m
merge = uncurry (<+>)

public export
interface Monoid m => Factorial m where
  Factor : m -> Type
  isFactor : (x : m) -> Dec (Factor x)
  factors : m -> List m
  factorsFactorIdentity : (x : m) -> {auto 0 okay : Factor x} -> (x :: Nil) = factors x

  Null : m -> Type
  isNull : (x : m) -> Dec (Null x)
  splitPrimePrefix : (x : m) -> Not (Null x) -> (m, m)
  splitPrimePrefixIsFactor : (x : m) -> (proof : Not (Null x)) -> Factor (fst (splitPrimePrefix x proof))
  splitPrimePrefixReversible : (x : m) -> (proof : Not (Null x)) -> merge (splitPrimePrefix x proof) = x

public export
data ListFactor : List a -> Type where
  IsListFactor : ListFactor (x :: Nil)

export
Uninhabited (ListFactor Nil) where
  uninhabited IsListFactor impossible

export
Uninhabited (ListFactor (x :: x' :: xs)) where
  uninhabited IsListFactor impossible

public export
data ListNull : List a -> Type where
  IsListNull : ListNull Nil

export
Uninhabited (ListNull (x :: xs)) where
  uninhabited IsListNull impossible

export
Factorial (List a) where
  Factor = ListFactor

  isFactor Nil = No absurd
  isFactor (x :: Nil) = Yes IsListFactor
  isFactor (x :: x' :: xs) = No absurd

  factors Nil = Nil
  factors (x :: xs) = [x] :: factors xs

  factorsFactorIdentity (x :: Nil) = Refl

  Null = ListNull

  isNull Nil = Yes IsListNull
  isNull (x :: xs) = No absurd

  splitPrimePrefix Nil proof = void $ proof $ IsListNull
  splitPrimePrefix (x :: xs) _ = ([x], xs)

  splitPrimePrefixIsFactor Nil proof = void $ proof $ IsListNull
  splitPrimePrefixIsFactor (x :: xs) proof = IsListFactor

  splitPrimePrefixReversible Nil proof = void $ proof $ IsListNull
  splitPrimePrefixReversible (x :: xs) proof = Refl
