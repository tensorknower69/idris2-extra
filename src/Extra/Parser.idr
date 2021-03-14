module Extra.Parser

import Data.Bits
import Data.DPair
import Data.List
import Debug.Trace
import Data.List1
import Data.String
import Extra.Alternative
import Extra.Applicative
import Extra.Char
import Extra.String
import Extra.Vect

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
  Monoid i => LazyApplicative (Parser i) where
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
string : (MonoListLike full item, MonoListLike full' item) => (Eq item) => full' -> Parser full full'
string xxs = case isNonEmpty xxs of
  No _ => pure xxs -- pure neutral
  Yes _ => let (x, xs) = uncons xxs in
    token x *> string xs *> pure xxs

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
digit : (MonoListLike full Char) => Parser full (Fin 10)
digit = More (Fail "digit") $ \i => case isNonEmpty i of
  No _ => digit
  Yes _ => let (x, xs) = uncons i in case x of {
    '0' => Done xs 0; '1' => Done xs 1; '2' => Done xs 2; '3' => Done xs 3; '4' => Done xs 4;
    '5' => Done xs 5; '6' => Done xs 6; '7' => Done xs 7; '8' => Done xs 8; '9' => Done xs 9;
    _ => Fail "digit"
  }

export
hexDigit : (MonoListLike full Char) => Parser full (Fin 16)
hexDigit = More (Fail "hexDigit") $ \i => case isNonEmpty i of
  No _ => hexDigit
  Yes _ => let (x, xs) = uncons i in case x of {
    '0' => Done xs 0; '1' => Done xs 1; '2' => Done xs 2; '3' => Done xs 3;
    '4' => Done xs 4; '5' => Done xs 5; '6' => Done xs 6; '7' => Done xs 7;
    '8' => Done xs 8; '9' => Done xs 9; 'A' => Done xs 10; 'B' => Done xs 11;
    'C' => Done xs 12; 'D' => Done xs 13; 'E' => Done xs 14; 'F' => Done xs 15;
    'a' => Done xs 10; 'b' => Done xs 11; 'c' => Done xs 12; 'd' => Done xs 13;
    'e' => Done xs 14; 'f' => Done xs 15;
    _ => Fail "hexDigit"
  }

export
octDigit : (MonoListLike full Char) => Parser full (Fin 8)
octDigit = More (Fail "octDigit") $ \i => case isNonEmpty i of
  No _ => octDigit
  Yes _ => let (x, xs) = uncons i in case x of {
    '0' => Done xs 0; '1' => Done xs 1; '2' => Done xs 2; '3' => Done xs 3;
    '4' => Done xs 4; '5' => Done xs 5; '6' => Done xs 6; '7' => Done xs 7;
    _ => Fail "octDigit"
  }
