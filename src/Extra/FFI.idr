module Extra.FFI

-- TODO: c int,uint is not guaranteed to be 32 bit

public export
SizeT : Type
SizeT = Bits32

public export
SSizeT : Type
SSizeT = Int

public export
CInt32 : Type
CInt32 = Int

public export
CUInt32 : Type
CUInt32 = Bits32

public export
CInt : Type
CInt = CInt32

public export
CUInt : Type
CUInt = CUInt32

public export
CByte : Type
CByte = Bits8

export
libc : String -> String
libc f = "C:" <+> f <+> ",libc"

export
libextra : String -> String
libextra f = "C:" <+> f <+> ",libextra"

export
%foreign libc "malloc"
prim__malloc : SizeT -> PrimIO AnyPtr

export
%foreign libc "free"
prim__free : AnyPtr -> PrimIO ()

export
%foreign libextra "peek"
prim__peek : AnyPtr -> SizeT -> PrimIO CByte

export
%foreign libextra "poke"
prim__poke : AnyPtr -> SizeT -> CByte -> PrimIO ()

export
nullanyptr : AnyPtr
nullanyptr = prim__getNullAnyPtr

export
nullptr : Ptr a
nullptr = prim__castPtr nullanyptr
