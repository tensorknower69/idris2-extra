module Extra.Applicative

import Data.Vect

infixl 3 <*>|, *>|, <*|

||| Lazy version of Applicative, provides `<*>|`
public export
interface Applicative f => LazyApplicative f where
  (<*>|) : f (a -> b) -> Lazy (f a) -> f b

||| Lazy version of `*>|`
export
(*>|) : LazyApplicative f => f a -> Lazy (f b) -> f b
a *>| b = map (const id) a <*>| b

||| Lazy version of `<*|`
export
(<*|) : LazyApplicative f => f a -> Lazy (f b) -> f a
a <*| b = map (\a => const a) a <*>| b

||| 'Execute' an applicative repeatedly for `n` times
export
count : Applicative f => (n : Nat) -> f a -> f (Vect n a)
count Z p = pure Nil
count (S n) p = (::) <$> p <*> count n p

||| 'Execute' an applicative and neglect the output
export
skip : Applicative f => f a -> f ()
skip p = p $> ()
