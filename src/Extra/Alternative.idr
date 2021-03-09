module Extra.Alternative

import Data.List1
import public Extra.Applicative

infixl 2 <|>|

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

export
manyTill : (LazyApplicative f, LazyAlternative f) => f a -> f b -> f (List a)
manyTill parser end = (end $> Nil) <|>| ((::) <$> parser <*>| manyTill parser end)
