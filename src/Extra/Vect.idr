module Extra.Vect

import public Data.Vect
import Data.List1
import Data.List

public export
toList1 : Vect (S n) a -> List1 a
toList1 (x :: xs) = x ::: toList xs
