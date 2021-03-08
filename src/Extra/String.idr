module Extra.String

import Data.String

-- TODO: I have no idea how should I be implementing this
public export
data NonEmpty : StrM xs -> Type where
  IsNonEmpty : {x : Char} -> {xs : String} -> NonEmpty (StrCons x xs)

export
Uninhabited (NonEmpty StrNil) where
  uninhabited IsNonEmpty impossible

-- public export
-- packUnpackId : (xs : String) -> pack (unpack xs) = xs
-- packUnpackId xs = believe_me (pack (unpack xs) = xs) ()
-- 
-- public export
-- reverseReverseId : (xs : String) -> xs = reverse (reverse xs)
-- reverseReverseId xs = believe_me (reverse (reverse xs)) ()
-- 
-- public export
-- testing : (x : Char) -> (xs : String) -> StrCons a as = strM (strCons a as)
-- testing = believe_me ()
-- 
-- reverseNonEmpty : (xs : String) -> NonEmpty () -> NonEmpty
