module Extra.Scientific

private
pow : Integer -> Integer -> Integer
pow a 0 = 1
pow a b = if b < 0 then 0 else a * pow a (b - 1)

private
bin10Index : Integer -> Integer
bin10Index n = helper 0
  where
  helper : Integer -> Integer
  helper a = if n < pow 10 a then a else helper (a + 1)

||| Scientific notation representation in the form of `coefficient*10^(exponentation)`
public export
data Scientific : Type where
  MkScientific : (coefficient : Integer) -> (exponentation : Integer) -> Scientific

export
Show Scientific where
  show (MkScientific m n) = show m <+> "e" <+> show n

export
Num Scientific where
  (MkScientific c1 e1) + (MkScientific c2 e2) =
    if e1 < e2
    then MkScientific (c1 + c2 * (10 `pow` (e2 - e1))) e1
    else MkScientific (c1 * (10 `pow` (e1 - e2)) + c2) e2
  (MkScientific m n) * (MkScientific m' n') = MkScientific (m * m') (n * n')
  fromInteger i = MkScientific i 0

export
Neg Scientific where
  negate (MkScientific c e) = MkScientific (-c) e

||| Convert a integer into a `Scientific` with its most significant digit moved to just after the decimal point
export
asDecimal : Integer -> Scientific
asDecimal n = MkScientific n (negate (bin10Index n))

export
toDouble : Scientific -> Double
toDouble (MkScientific m n) = cast m * (10 `pow` cast n)
