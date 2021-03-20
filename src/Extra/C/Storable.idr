module Extra.C.Storable

import Extra.C.FFI
import Extra.C.Types
import Extra.C.Float
import Extra.C.Ptr
import Data.List

export
interface Storable a where
  sizeOfType : SizeT
  peek : HasIO io => Ptr a -> io a
  poke : HasIO io => Ptr a -> a -> io ()

%foreign libextra "peek_uint8_t"
prim__peek_uint8_t : Ptr CUInt8 -> PrimIO CUInt8

%foreign libextra "poke_uint8_t"
prim__poke_uint8_t : Ptr CUInt8 -> CUInt8 -> PrimIO ()

%foreign libextra "peek_uint16_t"
prim__peek_uint16_t : Ptr CUInt16 -> PrimIO CUInt16

%foreign libextra "poke_uint16_t"
prim__poke_uint16_t : Ptr CUInt16 -> CUInt16 -> PrimIO ()

%foreign libextra "peek_uint32_t"
prim__peek_uint32_t : Ptr CUInt32 -> PrimIO CUInt32

%foreign libextra "poke_uint32_t"
prim__poke_uint32_t : Ptr CUInt32 -> CUInt32 -> PrimIO ()

%foreign libextra "peek_uint64_t"
prim__peek_uint64_t : Ptr CUInt64 -> PrimIO CUInt64

%foreign libextra "poke_uint64_t"
prim__poke_uint64_t : Ptr CUInt64 -> CUInt64 -> PrimIO ()

%foreign libextra "peek_int32_t"
prim__peek_int32_t : Ptr CInt32 -> PrimIO CInt32

%foreign libextra "poke_int32_t"
prim__poke_int32_t : Ptr CInt32 -> CInt32 -> PrimIO ()

%foreign libextra "peek_double_t"
prim__peek_double_t : Ptr CDouble -> PrimIO CDouble

%foreign libextra "poke_double_t"
prim__poke_double_t : Ptr CDouble -> CDouble -> PrimIO ()

export
Storable CInt32 where
  sizeOfType = 4
  peek ptr = primIO $ prim__peek_int32_t ptr
  poke ptr x = primIO $ prim__poke_int32_t ptr x

export
Storable CUInt8 where
  sizeOfType = 1
  peek ptr = primIO $ prim__peek_uint8_t ptr
  poke ptr x = primIO $ prim__poke_uint8_t ptr x

export
Storable CUInt16 where
  sizeOfType = 2
  peek ptr = primIO $ prim__peek_uint16_t ptr
  poke ptr x = primIO $ prim__poke_uint16_t ptr x

export
Storable CUInt32 where
  sizeOfType = 4
  peek ptr = primIO $ prim__peek_uint32_t ptr
  poke ptr x = primIO $ prim__poke_uint32_t ptr x

export
Storable CUInt64 where
  sizeOfType = 8
  peek ptr = primIO $ prim__peek_uint64_t ptr
  poke ptr x = primIO $ prim__poke_uint64_t ptr x

export
Storable CFloat where
  sizeOfType = 4
  peek ptr = primIO $ peekFloat ptr
  poke ptr x = primIO $ pokeFloat ptr x

export
Storable CDouble where
  sizeOfType = 8
  peek ptr = primIO $ prim__peek_double_t ptr
  poke ptr x = primIO $ prim__poke_double_t ptr x

export
withThe : (HasIO io, Storable a) => (Ptr a -> io b) -> io b
withThe f = do
  ptr <- primIO $ prim__malloc (sizeOfType {a=a})
  ret <- f (castPtr ptr)
  primIO $ prim__free ptr
  pure ret

export
pokeArray : (HasIO io, Storable a) => Ptr a -> List a -> io ()
pokeArray ptr Nil = pure ()
pokeArray ptr (x :: xs) = do
  poke ptr x
  pokeArray (plusPtr ptr (cast $ sizeOfType {a=a})) xs

export
withArray : (HasIO io, Storable a) => List a -> (Ptr a -> io b) -> io b
withArray list f = do
  let len = cast $ natToInteger $ length list
  ptr <- primIO $ prim__malloc (sizeOfType {a=a} * len)
  pokeArray (castPtr ptr) list
  ret <- f (castPtr ptr)
  primIO $ prim__free ptr
  pure ret

export
withCString : HasIO io => String -> (CString -> io a) -> io a
withCString str = withArray (map (cast . ord) (unpack str `snoc` '\0'))

export
peekArray : (HasIO io, Storable a) => SizeT -> Ptr a -> io (List a)
peekArray 0      ptr = pure []
peekArray length ptr = do
  x <- peek ptr
  let ptr' = plusPtr ptr (cast (sizeOfType {a=a}))
  let length' = cast $ cast {to = Integer} length - 1
  xs <- peekArray length' ptr'
  pure $ x :: xs

export
peekArray0 : (HasIO io, Storable a, Eq a) => a -> Ptr a -> io (List a)
peekArray0 end ptr = do
  x <- peek ptr
  case x == end of
    True => pure []
    False => do
      let ptr' = plusPtr ptr (cast (sizeOfType {a=a}))
      xs <- peekArray0 end ptr'
      pure $ x :: xs

export
peekCString : (HasIO io) => CString -> io String
peekCString ptr = do
  arr <- peekArray0 0 ptr
  pure $ pack $ map (chr . cast) arr
