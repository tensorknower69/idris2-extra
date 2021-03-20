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

export
%foreign libextra "ptr_eq"
prim__ptr_eq : AnyPtr -> AnyPtr -> PrimIO Bool

export
%foreign libextra "ptr_plus"
prim__ptr_plus : AnyPtr -> SSizeT -> PrimIO AnyPtr

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

export
Eq AnyPtr where
  a == b = unsafePerformIO $ primIO $ prim__ptr_eq a b

export
Eq (Ptr a) where
  a == b = forgetPtr a == forgetPtr b

||| `nullptr` in C
export
nullanyptr : AnyPtr
nullanyptr = prim__getNullAnyPtr

||| `nullptr` of a `Ptr` in C
export
nullptr : Ptr a
nullptr = castPtr nullanyptr

export
plusAnyPtr : AnyPtr -> (offset : SSizeT) -> AnyPtr
plusAnyPtr ptr ofs = unsafePerformIO $ primIO $ prim__ptr_plus ptr ofs

export
plusPtr : Ptr a -> (offset : SSizeT) -> Ptr a
plusPtr ptr ofs = castPtr $ plusAnyPtr (forgetPtr ptr) ofs
