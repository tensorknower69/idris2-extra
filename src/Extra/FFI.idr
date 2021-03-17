module Extra.FFI

-- TODO: c int,uint is not guaranteed to be 32 bit

||| `size_t in C`
public export
SizeT : Type
SizeT = Bits32

||| `ssize_t` in C
public export
SSizeT : Type
SSizeT = Int

||| `int32_t` in C
public export
CInt32 : Type
CInt32 = Int

||| `uint32_t` in C
public export
CUInt32 : Type
CUInt32 = Bits32

||| `int` in C
public export
CInt : Type
CInt = CInt32

||| `unsigned int` in C
public export
CUInt : Type
CUInt = CUInt32

||| `uint8_t` in C
public export
CUInt8 : Type
CUInt8 = Bits8

private
libc : String -> String
libc f = "C:" <+> f <+> ",libc"

private
libextra : String -> String
libextra f = "C:" <+> f <+> ",libextra"

||| `malloc` in C
export
%foreign libc "malloc"
prim__malloc : SizeT -> PrimIO AnyPtr

||| `free` in C
export
%foreign libc "free"
prim__free : AnyPtr -> PrimIO ()

||| Peek a byte in a ptr
export
%foreign libextra "peek"
prim__peek : AnyPtr -> SizeT -> PrimIO CUInt8

||| Poke a byte in a ptr
export
%foreign libextra "poke"
prim__poke : AnyPtr -> SizeT -> CUInt8 -> PrimIO ()

||| `nullptr` in C
export
nullanyptr : AnyPtr
nullanyptr = prim__getNullAnyPtr

||| `nullptr` of a `Ptr`
export
nullptr : Ptr a
nullptr = prim__castPtr nullanyptr
