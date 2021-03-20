module Extra.C.Ptr

import Extra.C.FFI
import public Extra.C.Types

||| `malloc` in C
export
%foreign libc "malloc"
prim__malloc : SizeT -> PrimIO AnyPtr

||| `calloc` in C
export
%foreign libc "calloc"
prim__calloc : SizeT -> PrimIO AnyPtr

||| `free` in C
export
%foreign libc "free"
prim__free : AnyPtr -> PrimIO ()

||| Peek a byte in a ptr
export
%foreign libextra "peek"
prim__peek : Ptr CUInt8 -> SizeT -> PrimIO CUInt8

||| Poke a byte in a ptr
export
%foreign libextra "poke"
prim__poke : Ptr CUInt8 -> SizeT -> CUInt8 -> PrimIO ()

export
%foreign libextra "ptr_eq"
prim__ptr_eq : AnyPtr -> AnyPtr -> PrimIO Bool

||| Pointer equal
export
anyPtrEq : HasIO io => AnyPtr -> AnyPtr -> io Bool
anyPtrEq a b = primIO $ prim__ptr_eq a b

||| cast pointer
export
castPtr : AnyPtr -> Ptr a
castPtr = prim__castPtr

||| forget pointer
export
forgetPtr : Ptr a -> AnyPtr
forgetPtr = prim__forgetPtr

export
pretendPtr : Ptr a -> Ptr b
pretendPtr = castPtr . forgetPtr

||| `nullptr` in C
export
nullanyptr : AnyPtr
nullanyptr = prim__getNullAnyPtr

||| `nullptr` of a `Ptr` in C
export
nullptr : Ptr a
nullptr = castPtr nullanyptr

export
isNullAnyPtr : AnyPtr -> Bool
isNullAnyPtr = (== 1) . prim__nullAnyPtr

export
isNullPtr : Ptr a -> Bool
isNullPtr = (== 1) . prim__nullPtr

export
peekPtr : HasIO io => Ptr CUInt8 -> SizeT -> io CUInt8
peekPtr ptr index = primIO $ prim__peek ptr index

export
pokePtr : HasIO io => Ptr CUInt8 -> SizeT -> CUInt8 -> io ()
pokePtr ptr index byte = primIO $ prim__poke ptr index byte
