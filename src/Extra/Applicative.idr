module Extra.Applicative

import Data.Vect

infixl 3 <*>|, *>|, <*|

public export
interface Applicative f => LazyApplicative f where
  (<*>|) : f (a -> b) -> Lazy (f a) -> f b

export
(*>|) : LazyApplicative f => f a -> Lazy (f b) -> f b
a *>| b = map (const id) a <*>| b

export
(<*|) : LazyApplicative f => f a -> Lazy (f b) -> f a
a <*| b = map (\a => const a) a <*>| b

export
count : Applicative f => (n : Nat) -> f a -> f (Vect n a)
count Z p = pure Nil
count (S n) p = (::) <$> p <*> count n p
