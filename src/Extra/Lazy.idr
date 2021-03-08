module Extra.Lazy

import Data.List1

-- TODO: This module doesn't feel right to me

infixl 3 <*>|, *>|, <*|
infixl 2 <|>|

public export
interface Applicative f => LazyApplicative f where
  (<*>|) : f (a -> b) -> Lazy (f a) -> f b

export
(*>|) : LazyApplicative f => f a -> Lazy (f b) -> f b
a *>| b = map (const id) a <*>| b

export
(<*|) : LazyApplicative f => f a -> Lazy (f b) -> f a
a <*| b = map (\a => const a) a <*>| b

public export
interface Alternative f => LazyAlternative f where
  (<|>|) : f a -> Lazy (f a) -> f a

export
manyLazy : (LazyApplicative f, LazyAlternative f) => f a -> f (List a)
manyLazy p = ((::) <$> p <*>| manyLazy p) <|> pure neutral

export
someLazy : (LazyApplicative f, LazyAlternative f) => f a -> f (List1 a)
someLazy p = (:::) <$> p <*>| manyLazy p

export
sepByLazy : (LazyApplicative f, LazyAlternative f) => f a -> f b -> f (List a)
sepByLazy parser seperator = (::) <$> parser <*>| ((seperator *>| sepByLazy parser seperator) <|> pure neutral)

export
sepBy1Lazy : (LazyApplicative f, LazyAlternative f) => f a -> f b -> f (List1 a)
sepBy1Lazy parser seperator = (:::) <$> parser <*>| ((seperator *> sepByLazy parser seperator) <|> pure neutral)
