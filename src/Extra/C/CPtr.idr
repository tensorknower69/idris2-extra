module Extra.C.CPtr

import Data.Nat
import Data.Vect
import Extra.String
import Extra.Proof
import Extra.C.Ptr
import Extra.C.Storable
import public Control.Linear.LIO
import public Extra.C.Types

public export
data Content : Type where
  NullTerminated : (can_free : Bool) -> Content
  Bytes : (can_free, can_read, can_write : Bool) -> Nat -> Content
  Opaque : (can_free : Bool) -> (ty : Type) -> Content

public export
isFreeable : Content -> Bool
isFreeable (NullTerminated can_free) = can_free
isFreeable (Bytes can_free _ _ _) = can_free
isFreeable (Opaque can_free _) = can_free

public export
typeOf : Content -> Type
typeOf (NullTerminated _) = CChar
typeOf (Bytes _ _ _ _) = CUInt8
typeOf (Opaque _ ty) = ty

public export
data CPtr : Content -> Type where
  MkCPtr : Ptr (typeOf content) -> CPtr content

export
malloc
  : LinearIO io
  => (length : Nat)
  -> {default True can_free : Bool}
  -> {default True can_read : Bool}
  -> {default True can_write : Bool}
  -> L io {use=1} (CPtr (Bytes can_free can_read can_write length))
malloc length = do
  ptr <- primIO $ prim__malloc $ cast $ natToInteger length
  pure1 $ MkCPtr (castPtr ptr)

export
calloc
  : LinearIO io
  => (length : Nat)
  -> {default True can_free : Bool}
  -> {default True can_read : Bool}
  -> {default True can_write : Bool}
  -> L io {use=1} (CPtr (Bytes can_free can_read can_write length))
calloc length = do
  ptr <- primIO $ prim__calloc $ cast $ natToInteger length
  pure1 $ MkCPtr (castPtr ptr)

export
free
  : LinearIO io
  => (1 _ : CPtr content)
  -> {auto okay : isFreeable content = True}
  -> L io ()
free (MkCPtr ptr) = primIO $ prim__free (forgetPtr ptr)

export
pokeByte
  : LinearIO io
  => (1 _ : CPtr (Bytes can_free can_read True length))
  -> (index : Nat)
  -> {auto 0 okay : LT index length}
  -> (byte : CUInt8)
  -> L io {use=1} (CPtr (Bytes can_free can_read True length))
pokeByte (MkCPtr ptr) index byte = do
  poke (plusPtr ptr (cast $ natToInteger index)) byte
  pure1 $ MkCPtr ptr

export
peekByte
  : LinearIO io
  => (1 _ : CPtr (Bytes can_free True can_write length))
  -> (index : Nat)
  -> {auto 0 okay : LT index length}
  -> L io {use=1} (Res CUInt8 (\_ => CPtr (Bytes can_free True can_write length)))
peekByte (MkCPtr ptr) index = do
  byte <- peek (plusPtr ptr (cast $ natToInteger index))
  pure1 $ (byte # MkCPtr ptr)

export
peekBytes
  : LinearIO io 
  => (1 _ : CPtr (Bytes can_free True can_write length))
  -> (offset : Nat)
  -> (count : Nat)
  -> {auto okay : LTE (offset + count) length}
  -> L io {use=1} (Res (Vect count CUInt8) (\_ => CPtr (Bytes can_free True can_write length)))
peekBytes cptr ofs Z = pure1 $ Nil # cptr
peekBytes cptr ofs (S cnt) = do
  let m = lteAddRight (S ofs) {m = cnt}
  let m = replace {p = LTE (S ofs)} (plusSuccRightSucc ofs cnt) m
  byte # cptr <- peekByte {okay = lteTransitive m okay} cptr ofs
  let n = okay
  let n = replace {p = \a => LTE a length} (sym $ plusSuccRightSucc ofs cnt) n
  bytes # cptr <- peekBytes cptr (S ofs) cnt {okay = n}
  pure1 $ (byte :: bytes) # cptr

export
pokeBytes
  : LinearIO io 
  => (1 _ : CPtr (Bytes can_free can_read True length))
  -> (offset : Nat)
  -> {count : Nat}
  -> (bytes : Vect count CUInt8)
  -> {auto okay : LTE (offset + count) length}
  -> L io {use=1} (CPtr (Bytes can_free can_read True length))
pokeBytes {count = Z} cptr ofs Nil             = pure1 $ cptr
pokeBytes {count = S cnt} cptr ofs (byte :: bytes) = do
  let m = lteAddRight (S ofs) {m = cnt}
  let m = replace {p = LTE (S ofs)} (plusSuccRightSucc ofs cnt) m
  cptr <- pokeByte {okay = lteTransitive m okay} cptr ofs byte
  let n = okay
  let n = replace {p = \a => LTE a length} (sym $ plusSuccRightSucc ofs cnt) n
  pokeBytes {okay = n} cptr (S ofs) bytes

export
unsafeToNullTerminated
  : LinearIO io
  => (1 _ : CPtr (Bytes can_free can_read can_write length))
  -> L io {use=1} (CPtr (NullTerminated can_free))
unsafeToNullTerminated (MkCPtr ptr) = pure1 $ MkCPtr ptr

export
unsafeToBytes
  : LinearIO io
  => (1 _ : CPtr (NullTerminated can_free))
  -> (0 length : Nat)
  -> {default True can_read  : Bool}
  -> {default True can_write : Bool}
  -> L io {use=1} (CPtr (Bytes can_free can_read can_write length))
unsafeToBytes (MkCPtr ptr) _ = pure1 $ MkCPtr ptr

-- TODO: behavior of length on strings containing '\0' is weird (?
export
packString
  : LinearIO io
  => String
  -> {default True can_free : Bool}
  -> L io {use=1} (CPtr (NullTerminated can_free))
packString str = do
  cptr <- malloc (S (length str))
  cptr <- pokeBytes {okay = believe_me ()} cptr 0 ((map (cast . ord) $ unpackVect str) `snoc` 0)
  let (MkCPtr ptr) = cptr
  pure1 $ MkCPtr ptr

export
packBytes
  : LinearIO io
  => {length : Nat}
  -> Vect length CUInt8
  -> {default True can_read  : Bool}
  -> {default True can_write : Bool}
  -> L io {use=1} (CPtr (Bytes True can_read can_write length))
packBytes bytes = do
  cptr <- malloc length
  cptr <- pokeBytes {okay = lteRefl} cptr 0 bytes
  let (MkCPtr ptr) = cptr
  pure1 $ MkCPtr ptr

export
unpackBytes
  : LinearIO io
  => {length : Nat}
  -> (1 _ : CPtr (Bytes can_free True can_write length))
  -> L io {use=1} (Res (Vect length CUInt8) (\_ => CPtr (Bytes can_free True can_write length)))
unpackBytes cptr = do
  bytes # cptr <- peekBytes {okay = lteRefl} cptr 0 length
  pure1 $ bytes # cptr
