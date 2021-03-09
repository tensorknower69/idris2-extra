module Extra.Parser

import Data.List
import Data.List1
import Data.String
import Extra.Alternative
import Extra.Vect
import Extra.Applicative
import Extra.Binary
import Extra.String

public export
interface MonoFoldable full item | full where
  foldl : (a -> item -> a) -> a -> full -> a
  foldr : (item -> b -> b) -> b -> full -> b

  foldl f = foldr (flip f)
  foldr f = foldl (flip f)

public export
interface (MonoFoldable full item, Monoid full) => MonoListLike full item | full where
  NonEmpty : full -> Type
  isNonEmpty : MonoListLike full item => (xs : full) -> Dec (NonEmpty xs)

  singleton : item -> full

  cons : item -> full -> full
  uncons : (xs : full) -> {auto 0 ok: NonEmpty xs} -> (item, full)

  head : (xs : full) -> {auto 0 ok : NonEmpty xs} -> item
  tail : (xs : full) -> {auto 0 ok : NonEmpty xs} -> full

  init : (xs : full) -> {auto 0 ok : NonEmpty xs} -> full
  last : (xs : full) -> {auto 0 ok : NonEmpty xs} -> item

  null : full -> Lazy Bool
  length : full -> Nat

  toList : full -> List item
  toList full =
    case isNonEmpty full of
      No _ => neutral
      Yes _ => let (a, as) = uncons full in a :: toList as

  fromList : List item -> full
  fromList [] = neutral
  fromList (x :: xs) = cons x (fromList xs)

export
{0 a : Type} -> MonoFoldable (List a) a where
  foldl = Prelude.foldl
  foldr = Prelude.foldr

export
{0 a : Type} -> MonoListLike (List a) a where
  NonEmpty = Data.List.NonEmpty

  isNonEmpty (x :: xs) = Yes IsNonEmpty
  isNonEmpty Nil = No absurd

  singleton = pure

  cons x xs = x :: xs
  uncons (x :: xs) = (x, xs)

  head = Data.List.head
  tail = Data.List.tail

  init = Data.List.init
  last = Data.List.last

  null = Prelude.null
  length = Prelude.List.length

export
MonoFoldable String Char where
  foldl f a = Extra.Parser.foldl f a . fastUnpack

export
MonoListLike String Char where
  NonEmpty xs = Extra.String.NonEmpty (strM xs)
  isNonEmpty xs = case strM xs of
    StrNil => No absurd
    StrCons a as => Yes (believe_me (Extra.String.IsNonEmpty {x = a, xs = as}))

  singleton = Data.String.singleton

  cons a as = strCons a as
  uncons xs = case strM xs of StrCons a as => (a, as)

  head xs = case strM xs of StrCons a as => a
  tail xs = case strM xs of StrCons a as => as
  init xs = case strM xs of
    StrCons a as => case isNonEmpty as of
      No _ => singleton a
      Yes _ => cons a (init as)
  last xs = case strM xs of
    StrCons a as => case isNonEmpty as of
      No _ => a
      Yes _ => last as

  length = Prelude.String.length
  null "" = True
  null _ = False

export
data Parser : (input_type: Type) -> (result : Type) -> Type where
  Done : (leftover : i) -> (result : r) -> Parser i r
  Fail : (msg : String) -> Parser i r
  More : (on_eof : Lazy (Parser i r)) -> (on_feed : (i -> Parser i r)) -> Parser i r

-- core

export
fail : String -> Parser i r
fail = Fail

export
done : i -> r -> Parser i r
done = Done

export
more : (on_eof : Lazy (Parser i r)) -> (on_feed : (i -> Parser i r)) -> Parser i r
more = More

export
toEither : Parser i r -> Either String (i, r)
toEither (Done i r) = Right (i, r)
toEither (Fail msg) = Left msg
toEither (More _ _) = Left "partial"

export
toEither_ : Parser i r -> Either String r
toEither_ = map snd . toEither

export
feed : Semigroup i => i -> Parser i r -> Parser i r
feed input (Done leftover result) = Done (leftover <+> input) result
feed input (More _ on_feed) = on_feed input
feed input (Fail msg) = Fail msg

export
feedEof : Parser i r -> Parser i r
feedEof (Done leftover result) = Done leftover result
feedEof (More on_eof _) = on_eof
feedEof (Fail msg) = Fail msg

infixl 0 <?>

export
(<?>) : Parser i r -> String -> Parser i r
(Fail msg') <?> msg = Fail $ msg <+> "." <+> msg'
(Done leftover result) <?> _ = Done leftover result
(More on_eof on_feed) <?> msg = More (on_eof <?> msg) (\i => on_feed i <?> msg)

export
Functor (Parser i) where
  map f (Done leftover result) = Done leftover (f result)
  map f (More on_eof on_feed) = More (map f on_eof) (map f . on_feed)
  map f (Fail msg) = Fail msg

mutual
  export
  (Semigroup i, Applicative (Parser i)) => LazyApplicative (Parser i) where
    (Done leftover f) <*>| p = map f (feed leftover p)
    (More on_eof_f on_feed_f) <*>| p = More (on_eof_f <*>| p) (\i => on_feed_f i <*>| p)
    (Fail msg) <*>| p = Fail msg

  export
  Monoid i => Applicative (Parser i) where
    pure = Done neutral
    a <*> b = a <*>| b

export
(Monoid i, Applicative (Parser i)) => Monad (Parser i) where
  (Done leftover result) >>= f = feed leftover (f result)
  (More on_eof on_feed) >>= f = More (on_eof >>= f) (\i => on_feed i >>= f)
  (Fail msg) >>= _ = Fail msg

mutual
  export
  (Semigroup i, Applicative (Parser i)) => LazyAlternative (Parser i) where
    (Done leftover result) <|>| p = Done leftover result
    (Fail msg) <|>| p = p
    p1 <|>| p2 = More (feedEof p1 <|>| feedEof p2) (\i => feed i p1 <|>| feed i p2)

  export
  (Semigroup i, Applicative (Parser i)) => Alternative (Parser i) where
    empty = Fail "empty"
    a <|> b = a <|>| b

-- basic

export
anyToken : MonoListLike full item => Parser full item
anyToken = More (Fail "anyToken") $ \i =>
  case isNonEmpty i of
    No _ => anyToken
    Yes _ => let (result, leftover) = uncons i in Done leftover result

export
satisfy : MonoListLike full item => (item -> Bool) -> Parser full item
satisfy predicate = More (Fail "satisfy") $ \i =>
  case isNonEmpty i of
    No _ => satisfy predicate
    Yes _ => let (token, leftover) = uncons i in
      if predicate token then Done leftover token else Fail "satisfy"

export
eof : Monoid i => Parser i ()
eof = More (Done neutral ()) (\_ => Fail "eof")

export
token : (MonoListLike full item, Eq item) => item -> Parser full item
token c = satisfy (c ==) <?> "token"

export
lookAhead : MonoListLike full item => Parser full item
lookAhead = More (Fail "lookAhead") $ \full =>
  case isNonEmpty full of
    No _ => lookAhead
    Yes _ => case uncons full of
      (x, xs) => Done full x

export
notFollowedBy : Monoid full => Parser full a -> Parser full ()
notFollowedBy = lookAheadNotInto neutral
  where
  lookAheadNotInto : full -> Parser full a -> Parser full ()
  lookAheadNotInto i parser =
    case parser of
      Fail _ => Done i ()
      More on_eof on_feed => More (lookAheadNotInto i on_eof) (\i' => lookAheadNotInto (i <+> i') (on_feed i'))
      Done _ _ => Fail "notFollowedBy"

-- show

export
showWith : Show i => ((i -> Parser i r) -> String) -> (r -> String) -> Parser i r -> String
showWith show_on_feed show_result parser =
  case parser of
    Done i r => "Done " <+> show i <+> " " <+> show_result r
    More on_eof on_feed => "More " <+> show_on_feed on_feed  <+> " or else " <+> showWith show_on_feed show_result on_eof
    Fail msg => "Fail " <+> msg

export
(Show i, Show r) => Show (Parser i r) where
  show = showWith (const "...") show

-- char stuff

export
lower : (MonoListLike full Char) => Parser full Char
lower = satisfy isLower

export
upper : (MonoListLike full Char) => Parser full Char
upper = satisfy isUpper

export
alpha : (MonoListLike full Char) => Parser full Char
alpha = satisfy isAlpha

export
alphaNum : (MonoListLike full Char) => Parser full Char
alphaNum = satisfy isAlphaNum

export
newline : (MonoListLike full Char) => Parser full Char
newline = satisfy isNL

export
space : (MonoListLike full Char) => Parser full Char
space = satisfy isSpace

export
digit : (MonoListLike full Char) => Parser full Char
digit = satisfy isDigit

export
hexDigit : (MonoListLike full Char) => Parser full Char
hexDigit = satisfy isHexDigit

export
octDigit : (MonoListLike full Char) => Parser full Char
octDigit = satisfy isHexDigit

-- binary stuff

export
zro : MonoListLike full Digit => Parser full Digit
zro = token O

export
one : MonoListLike full Digit => Parser full Digit
one = token I

infixl 1 >$=
-- TODO: can do without (Monoid full)
export
(>$=) : (Monoid full, MonoListLike full item) => Parser full a -> (a -> Either String b) -> Parser full b
m >$= f = map f m >>= \r => case r of
  Left msg => Fail msg
  Right r => pure r
-- utf8 stuff, TODO: better implementation

export
bits8BinPadToLen : MonoListLike full Bits8 => Parser full Bin
bits8BinPadToLen = (padToLen 8 . toBin . cast) <$> anyToken

export
utf8Code : (Monoid full, MonoListLike full Bits8) => Parser full Char
utf8Code = utf8Code4 <|> utf8Code3 <|> utf8Code2 <|> utf8Code1
  where
  binToChar : Bin -> Char
  binToChar = chr . toInt

  utf8AtomBin : Parser full Bin
  utf8AtomBin = bits8BinPadToLen >$= \r => toEither_ $ feed r $ ((toList <$> count 6 anyToken) <* zro <* one)
  
  utf8Code1 : Parser full Char
  utf8Code1 = (\a => binToChar a)
    <$> guard
    where
    guard : Parser full Bin
    guard = bits8BinPadToLen >$= \r => toEither_ $ feed r $ ((toList <$> count 7 anyToken) <* zro)
  
  utf8Code2 : Parser full Char
  utf8Code2 = (\a, b => binToChar $ b <+> a)
    <$> guard <*> utf8AtomBin
    where
    guard : Parser full Bin
    guard = bits8BinPadToLen >$= \r => toEither_ $ feed r $ ((toList <$> count 5 anyToken) <* zro <* one <* one)
  
  utf8Code3 : Parser full Char
  utf8Code3 = (\a, b, c => binToChar $ c <+> b <+> a)
    <$> guard <*> utf8AtomBin <*> utf8AtomBin
    where
    guard : Parser full Bin
    guard = bits8BinPadToLen >$= \r => toEither_ $ feed r $ ((toList <$> count 4 anyToken) <* zro <* one <* one <* one)
  
  utf8Code4 : Parser full Char
  utf8Code4 = (\a, b, c, d => binToChar $ d <+> c <+> b <+> a)
    <$> guard <*> utf8AtomBin <*> utf8AtomBin <*> utf8AtomBin
    where
    guard : Parser full Bin
    guard = bits8BinPadToLen >$= \r => toEither_ $ feed r $ ((toList <$> count 3 anyToken) <* zro <* one <* one <* one <* one)

export
charToUtf8 : Char -> List Bits8
charToUtf8 chr =
  let x = cast {to = Bits32} (ord chr) in
  if 0x0000 <= x && x <= 0x007F then
    [ prim__or_Bits8 0b00000000 $ prim__and_Bits8 0b01111111 $ cast (x `prim__shr_Bits32`  0)
    ]
  else if 0x0080 <= x && x <= 0x07FF then
    [ prim__or_Bits8 0b11000000 $ prim__and_Bits8 0b00011111 $ cast (x `prim__shr_Bits32`  6)
    , prim__or_Bits8 0b10000000 $ prim__and_Bits8 0b00111111 $ cast (x `prim__shr_Bits32`  0)
    ]
  else if 0x0800 <= x && x <= 0xFFFF then
    [ prim__or_Bits8 0b11100000 $ prim__and_Bits8 0b00001111 $ cast (x `prim__shr_Bits32` 12)
    , prim__or_Bits8 0b10000000 $ prim__and_Bits8 0b00111111 $ cast (x `prim__shr_Bits32`  6)
    , prim__or_Bits8 0b10000000 $ prim__and_Bits8 0b00111111 $ cast (x `prim__shr_Bits32`  0)
    ]
  else if 0x10000 <= x && x <= 0x10FFFF then
    [ prim__or_Bits8 0b11110000 $ prim__and_Bits8 0b00000111 $ cast (x `prim__shr_Bits32` 18)
    , prim__or_Bits8 0b10000000 $ prim__and_Bits8 0b00111111 $ cast (x `prim__shr_Bits32` 12)
    , prim__or_Bits8 0b10000000 $ prim__and_Bits8 0b00111111 $ cast (x `prim__shr_Bits32`  6)
    , prim__or_Bits8 0b10000000 $ prim__and_Bits8 0b00111111 $ cast (x `prim__shr_Bits32`  0)
    ]
  else
    [ 0b00000000
    ]
