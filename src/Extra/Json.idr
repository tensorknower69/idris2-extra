module Extra.Json

-- reference: https://www.json.org/json-en.html

import Extra.Parser
import Extra.Alternative
import Extra.Scientific
import Extra.Applicative
import Debug.Trace
import Data.Fin
import Data.List

public export
Number : Type
Number = Double

public export
data Value : Type where
  MkString : String -> Value
  MkObject : List (String, Value) -> Value
  MkArray : List Value -> Value
  MkNumber : Scientific -> Value
  MkBoolean : Bool -> Value
  MkNull : Value

export
Show Value where
  show (MkString str) = show str
  show (MkNumber scientific) = show scientific
  show (MkArray array) = "[" <+> (concat $ intersperse "," $ map show array) <+> "]"
  show (MkObject obj) = "{" <+> (concat $ intersperse "," $ map (\(a, b) => show a <+> ":" <+> show b) obj) <+> "}"
  show (MkBoolean False) = "false"
  show (MkBoolean True) = "true"
  show MkNull = "null"

export
oneNineP : Stream i Char => Parser i Integer
oneNineP = (token '1' $> 1) <|> (token '2' $> 2) <|> (token '3' $> 3)
       <|> (token '4' $> 4) <|> (token '5' $> 5) <|> (token '6' $> 6)
       <|> (token '7' $> 7) <|> (token '8' $> 8) <|> (token '9' $> 9)

export
digitP : Stream i Char => Parser i Integer
digitP = (token '0' $> 0) <|> oneNineP

export
digitsP : Stream i Char => Parser i Integer
digitsP = map snd helper
  where
  helper : Parser i (Integer, Integer)
  helper = do
    d <- digitP
    maybe_ds <- optional helper
    case maybe_ds of
      Nothing => pure (1, d)
      Just (n, ds) => let n' = n * 10 in pure (n', d * n' + ds)

export
integerP : Stream i Char => Parser i Integer
integerP = do
  b <- option 1 (token '-' $> (-1))
  n <- (token '0' $> 0) <|> digitsP
  pure $ b * n

export
signP : Stream i Char => Parser i Integer
signP = (token '+' $> 1) <|> (token '-' $> -1)

export
numberP : Stream i Char => Parser i Scientific
numberP = do
  pre <- integerP
  dec <- option 0 $ token '.' *> digitsP
  exp <- option 0 $ (token 'e' <|> token 'E') *> ((*) <$> (signP <|> pure 1) <*> digitsP)
  let a = MkScientific pre exp
  let b = asDecimal dec
  pure $ a + if pre < 0 then -b else b

export
whitespaceP : Stream i Char => Parser i ()
whitespaceP = many space $> ()

export
boolP : Stream i Char => Parser i Bool
boolP = (string "true" $> True) <|> (string "false" $> False)

export
escapeP : Stream i Char => Parser i Char
escapeP = (token '\\')
  <|> (token '/')
  <|> (token 'b' $> '\b')
  <|> (token 'f' $> '\f')
  <|> (token 'n' $> '\n')
  <|> (token 'r' $> '\r')
  <|> (token 't' $> '\t')

export
characterP : Stream i Char => Parser i Char
characterP = notFollowedBy (token '"') *> ((token '\\' *> escapeP) <|> utf16 <|> (notFollowedBy (token '\\') *> anyToken))
  where
  hex : Parser i Int
  hex = (cast . finToInteger) <$> hexDigit
  code : Parser i Int
  code = do
    skip (token '\\' *> token 'u')
    b1 <- hex; b2 <- hex; b3 <- hex; b4 <- hex
    pure $ b1 * 0x1000 + b2 * 0x100 + b3 * 0x10 + b4
  utf16 : Parser i Char
  utf16 = do
    code >>= \high => case (0xD800 <= high && high <= 0xDBFF) of
      False => pure $ chr high
      True => code >>= \low => case 0xDC00 <= low && low <= 0xDFFF of
        False => fail "utf16 no low surrogate"
        True => pure $ chr $ 0x10000 + (high - 0xD800) * 0x400 + (low - 0xDC00)

export
charactersP : Stream i Char => Parser i String
charactersP = (strCons <$> characterP <*>| charactersP) <|> pure neutral

export
stringP : Stream i Char => Parser i String
stringP = token '"' *> charactersP <* token '"'

export
nullP : Stream i Char => Parser i Value
nullP = string "null" $> MkNull

mutual
  export
  elementP : Stream i Char => Parser i Value
  elementP = whitespaceP *> valueP <* whitespaceP

  export
  elementsP : Stream i Char => Parser i (List Value)
  elementsP =
    ((::) <$> elementP <*>| (token ',' *> elementsP))
    <|> (pure <$> elementP)

  export
  memberP : Stream i Char => Parser i (String, Value)
  memberP = (,) <$> (whitespaceP *> stringP <* whitespaceP) <*> (token ':' *> elementP)

  export
  membersP : Stream i Char => Parser i (List (String, Value))
  membersP = ((::) <$> memberP <*>| (token ',' *> membersP)) <|> (pure <$> memberP)

  export
  arrayP : Stream i Char => Parser i (List Value)
  arrayP = (token '[' *> (whitespaceP $> []) <* token ']')
       <|> (token '[' *> elementsP <* token ']')

  export
  objectP : Stream i Char => Parser i (List (String, Value))
  objectP = (token '{' *> (whitespaceP $> []) <* token '}')
        <|> (token '{' *> membersP <* token '}')

  export
  valueP : Stream i Char => Parser i Value
  valueP = whitespaceP *> ((MkString <$> stringP)
                       <|> (MkNumber <$> numberP)
                       <|> (MkArray <$> arrayP))
                       <|> (MkBoolean <$> boolP)
                       <|> (MkObject <$> objectP)
                       <|> nullP
