module Extra.Nat

import Data.Fin

public export
subtract : (n : Nat) -> Fin (S n) -> Nat
subtract n FZ = n
subtract (S n) (FS k) = subtract n k
