module Extra.C.Types

-- TODO: c int,uint is not guaranteed to be 32 bit

export
data Float : Type where [external]

public export
CUInt8 : Type
CUInt8 = Bits8

public export
CUInt16 : Type
CUInt16 = Bits16

public export
CUInt32 : Type
CUInt32 = Bits32

public export
CUInt64 : Type
CUInt64 = Bits64

||| `size_t in C`
public export
SizeT : Type
SizeT = Bits32

||| `ssize_t` in C
public export
SSizeT : Type
SSizeT = Int

public export
CInt32 : Type
CInt32 = Int

||| `int` in C
public export
CInt : Type
CInt = Int

||| `unsigned int` in C
public export
CUInt : Type
CUInt = CUInt32

public export
CChar : Type
CChar = Bits8

public export
CUChar : Type
CUChar = Bits8

public export
CString : Type
CString = Ptr CChar

public export
CDouble : Type
CDouble = Double

--- TODO: this is unholy
||| `SizeT` but uses `Int` for `Data.Int.Order` reasons
public export
SizeInt : Type
SizeInt = Int
