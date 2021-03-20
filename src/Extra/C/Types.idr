module Extra.C.Types

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

public export
CChar : Type
CChar = Bits8

public export
CUChar : Type
CUChar = Bits8

public export
CString : Type
CString = Ptr CChar

--- TODO: this is unholy
||| `SizeT` but uses `Int` for `Data.Int.Order` reasons
public export
SizeInt : Type
SizeInt = Int
