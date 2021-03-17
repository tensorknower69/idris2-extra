module Extra.Parser

import Data.Bits
import Data.DPair
import Data.List
import Debug.Trace
import Data.List1
import Data.String
import Extra.Alternative
import Extra.Applicative
import Extra.String
import Extra.Vect

||| `Stream i e` where `i` is the full type and `e` is the type of a single token
public export
interface Monoid i => Stream i e | i where
  uncons : i -> Maybe (i, e)

export
{0 a : Type} -> Stream (List a) a where
  uncons Nil = Nothing
  uncons (x :: xs) = Just (xs, x)

export
Stream String Char where
  uncons xs = case strM xs of
    StrCons x xs => Just (xs, x)
    StrNil => Nothing

export
data Parser : (input: Type) -> (result : Type) -> Type where
  Done : (leftover : i) -> (result : r) -> Parser i r
  Fail : (msg : String) -> Parser i r
  More : (on_eof : Lazy (Parser i r)) -> (on_feed : (i -> Parser i r)) -> Parser i r

-- core
||| Fail a `Parser`, equivalent to the `Fail` constructor
export
fail : String -> Parser i r
fail = Fail

export
||| Complete a `Parser`, equivalent to the `Done` constructor, arguments:
||| - remaining input
||| - result value
done : i -> r -> Parser i r
done = Done

||| Create a `Parser` handling `feedEof`/`feed` cases, equivalent to the `More` constructor
export
more : (on_eof : Lazy (Parser i r)) -> (on_feed : (i -> Parser i r)) -> Parser i r
more = More

||| Convert a `Parser` into an Either, if the parser is partial, the result is `Left "partial"`
export
toEither : Parser i r -> Either String (i, r)
toEither (Done i r) = Right (i, r)
toEither (Fail msg) = Left msg
toEither (More _ _) = Left "partial"

||| `toEither` but discards the leftover
export
toEither_ : Parser i r -> Either String r
toEither_ = map snd . toEither

||| Feed a parser with inputs into a `Parser`
export
feed : Semigroup i => i -> Parser i r -> Parser i r
feed input (Done leftover result) = Done (leftover <+> input) result
feed input (More _ on_feed) = on_feed input
feed input (Fail msg) = Fail msg

||| Feed an EOF signal into a `Parser`
export
feedEof : Parser i r -> Parser i r
feedEof (Done leftover result) = Done leftover result
feedEof (More on_eof _) = on_eof
feedEof (Fail msg) = Fail msg

infixl 0 <?>

-- TODO: improve quality of labels
||| Labels a parser
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
anyToken : Stream i e => Parser i e
anyToken = More (Fail "anyToken") $ \i =>
  case uncons i of
    Nothing => anyToken
    Just (i', result) => Done i' result

export
satisfy : Stream i e => (e -> Bool) -> Parser i e
satisfy predicate = More (Fail "satisfy") $ \i =>
  case uncons i of
    Nothing => satisfy predicate
    Just (i', token) => if predicate token then Done i' token else Fail "satisfy"

export
eof : Monoid i => Parser i ()
eof = More (Done neutral ()) (\_ => Fail "eof")

export
token : (Stream i e, Eq e) => e -> Parser i e
token c = satisfy (c ==) <?> "token"

export
string : (Stream i e, Stream i' e) => (Eq e) => i' -> Parser i i'
string xxs = case uncons xxs of
  Nothing => pure xxs -- pure neutral
  Just (xs, x) => token x *> string xs *> pure xxs

export
lookAhead : Stream i e => Parser i e
lookAhead = More (Fail "lookAhead") $ \i =>
  case uncons i of
    Nothing => lookAhead
    Just (xs, x) => Done i x

export
notFollowedBy : Monoid i => Parser i a -> Parser i ()
notFollowedBy = lookAheadNotInto neutral
  where
  lookAheadNotInto : i -> Parser i a -> Parser i ()
  lookAheadNotInto i parser =
    case parser of
      Fail _ => Done i ()
      More on_eof on_feed => More (lookAheadNotInto i on_eof) (\i' => lookAheadNotInto (i <+> i') (on_feed i'))
      Done _ _ => Fail "notFollowedBy"

export
acceptAll : Monoid i => Parser i i
acceptAll = More (pure neutral) $ \i => (<+> i) <$> acceptAll

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
lower : (Stream i Char) => Parser i Char
lower = satisfy isLower

export
upper : (Stream i Char) => Parser i Char
upper = satisfy isUpper

export
alpha : (Stream i Char) => Parser i Char
alpha = satisfy isAlpha

export
alphaNum : (Stream i Char) => Parser i Char
alphaNum = satisfy isAlphaNum

export
newline : (Stream i Char) => Parser i Char
newline = satisfy isNL

export
space : (Stream i Char) => Parser i Char
space = satisfy isSpace

export
digit : (Stream i Char) => Parser i (Fin 10)
digit = More (Fail "digit") $ \i => case uncons i of
  Nothing => digit
  Just (xs, x) => case x of {
    '0' => Done xs 0; '1' => Done xs 1; '2' => Done xs 2; '3' => Done xs 3; '4' => Done xs 4;
    '5' => Done xs 5; '6' => Done xs 6; '7' => Done xs 7; '8' => Done xs 8; '9' => Done xs 9;
    _ => Fail "digit"
  }

export
hexDigit : (Stream i Char) => Parser i (Fin 16)
hexDigit = More (Fail "digit") $ \i => case uncons i of
  Nothing => hexDigit
  Just (xs, x) => case x of {
    '0' => Done xs 0; '1' => Done xs 1; '2' => Done xs 2; '3' => Done xs 3;
    '4' => Done xs 4; '5' => Done xs 5; '6' => Done xs 6; '7' => Done xs 7;
    '8' => Done xs 8; '9' => Done xs 9; 'A' => Done xs 10; 'B' => Done xs 11;
    'C' => Done xs 12; 'D' => Done xs 13; 'E' => Done xs 14; 'F' => Done xs 15;
    'a' => Done xs 10; 'b' => Done xs 11; 'c' => Done xs 12; 'd' => Done xs 13;
    'e' => Done xs 14; 'f' => Done xs 15;
    _ => Fail "hexDigit"
  }

export
octDigit : (Stream i Char) => Parser i (Fin 8)
octDigit = More (Fail "digit") $ \i => case uncons i of
  Nothing => octDigit
  Just (xs, x) => case x of {
    '0' => Done xs 0; '1' => Done xs 1; '2' => Done xs 2; '3' => Done xs 3;
    '4' => Done xs 4; '5' => Done xs 5; '6' => Done xs 6; '7' => Done xs 7;
    _ => Fail "octDigit"
  }
