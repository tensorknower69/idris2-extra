module Extra.Alternative

import Data.List1
import public Extra.Applicative

infixl 2 <|>|

public export
interface Alternative f => LazyAlternative f where
  (<|>|) : f a -> Lazy (f a) -> f a

export
many : (LazyApplicative f, Alternative f) => f a -> f (List a)
many p = ((::) <$> p <*>| many p) <|> pure neutral

export
some : (LazyApplicative f, Alternative f) => f a -> f (List1 a)
some p = (:::) <$> p <*>| many p

export
sepBy : (LazyApplicative f, Alternative f) => f a -> f b -> f (List a)
sepBy parser seperator = (::) <$> parser <*>| ((seperator *>| sepBy parser seperator) <|> pure neutral)

export
sepBy1 : (LazyApplicative f, Alternative f) => f a -> f b -> f (List1 a)
sepBy1 parser seperator = (:::) <$> parser <*>| ((seperator *> sepBy parser seperator) <|> pure neutral)

export
manyTill : (LazyApplicative f, LazyAlternative f) => f a -> f b -> f (List a)
manyTill parser end = (end $> Nil) <|>| ((::) <$> parser <*>| manyTill parser end)

export
option : Alternative f => (defaultsTo : a) -> f a -> f a
option def f = f <|> pure def

export
optional : Alternative f => f a -> f (Maybe a)
optional f = option Nothing (Just <$> f)
