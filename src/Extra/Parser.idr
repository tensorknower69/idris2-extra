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

public export
interface Monoid state => Stream state item | state where
  uncons : state -> Maybe (state, item)

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
anyToken : Stream state item => Parser state item
anyToken = More (Fail "anyToken") $ \state =>
  case uncons state of
    Nothing => anyToken
    Just (state', result) => Done state' result

export
satisfy : Stream state item => (item -> Bool) -> Parser state item
satisfy predicate = More (Fail "satisfy") $ \state =>
  case uncons state of
    Nothing => satisfy predicate
    Just (state', token) => if predicate token then Done state' token else Fail "satisfy"

export
eof : Monoid i => Parser i ()
eof = More (Done neutral ()) (\_ => Fail "eof")

export
token : (Stream state item, Eq item) => item -> Parser state item
token c = satisfy (c ==) <?> "token"

export
string : (Stream state item, Stream state' item) => (Eq item) => state' -> Parser state state'
string xxs = case uncons xxs of
  Nothing => pure xxs -- pure neutral
  Just (xs, x) => token x *> string xs *> pure xxs

export
lookAhead : Stream state item => Parser state item
lookAhead = More (Fail "lookAhead") $ \state =>
  case uncons state of
    Nothing => lookAhead
    Just (xs, x) => Done state x

export
notFollowedBy : Monoid state => Parser state a -> Parser state ()
notFollowedBy = lookAheadNotInto neutral
  where
  lookAheadNotInto : state -> Parser state a -> Parser state ()
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
lower : (Stream state Char) => Parser state Char
lower = satisfy isLower

export
upper : (Stream state Char) => Parser state Char
upper = satisfy isUpper

export
alpha : (Stream state Char) => Parser state Char
alpha = satisfy isAlpha

export
alphaNum : (Stream state Char) => Parser state Char
alphaNum = satisfy isAlphaNum

export
newline : (Stream state Char) => Parser state Char
newline = satisfy isNL

export
space : (Stream state Char) => Parser state Char
space = satisfy isSpace

export
digit : (Stream state Char) => Parser state (Fin 10)
digit = More (Fail "digit") $ \state => case uncons state of
  Nothing => digit
  Just (xs, x) => case x of {
    '0' => Done xs 0; '1' => Done xs 1; '2' => Done xs 2; '3' => Done xs 3; '4' => Done xs 4;
    '5' => Done xs 5; '6' => Done xs 6; '7' => Done xs 7; '8' => Done xs 8; '9' => Done xs 9;
    _ => Fail "digit"
  }

export
hexDigit : (Stream state Char) => Parser state (Fin 16)
hexDigit = More (Fail "digit") $ \state => case uncons state of
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
octDigit : (Stream state Char) => Parser state (Fin 8)
octDigit = More (Fail "digit") $ \state => case uncons state of
  Nothing => octDigit
  Just (xs, x) => case x of {
    '0' => Done xs 0; '1' => Done xs 1; '2' => Done xs 2; '3' => Done xs 3;
    '4' => Done xs 4; '5' => Done xs 5; '6' => Done xs 6; '7' => Done xs 7;
    _ => Fail "octDigit"
  }
