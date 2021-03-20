module Extra.C.Float

import Extra.C.FFI
import Extra.C.Types

-- DO NOT public export, otherwise it will be evaluated to canonical form
export
CFloat : Type
CFloat = Bits32

%foreign libextra "double_to_cfloat"
export
prim__double_to_cfloat : CDouble -> PrimIO CFloat

%foreign libextra "cfloat_to_double"
export
prim__cfloat_to_double : CFloat -> PrimIO CDouble

%foreign libextra "cfloat_add"
export
prim__cfloat_add : CFloat -> CFloat -> PrimIO CFloat

%foreign libextra "cfloat_sub"
export
prim__cfloat_sub : CFloat -> CFloat -> PrimIO CFloat

%foreign libextra "cfloat_neg"
export
prim__cfloat_neg : CFloat -> PrimIO CFloat

%foreign libextra "cfloat_mul"
export
prim__cfloat_mul : CFloat -> CFloat -> PrimIO CFloat

%foreign libextra "cfloat_div"
export
prim__cfloat_div : CFloat -> CFloat -> PrimIO CFloat

%foreign libextra "cfloat_recip"
export
prim__cfloat_recip : CFloat -> PrimIO CFloat

%foreign libextra "cfloat_abs"
export
prim__cfloat_abs : CFloat -> PrimIO CFloat

%foreign libextra "peek_float_t"
prim__peek_float_t : Ptr CFloat -> PrimIO CFloat

%foreign libextra "poke_float_t"
prim__poke_float_t : Ptr CFloat -> CFloat -> PrimIO ()

export
peekFloat : Ptr CFloat -> PrimIO CFloat
peekFloat ptr = prim__peek_float_t ptr

export
pokeFloat : Ptr CFloat -> CFloat -> PrimIO ()
pokeFloat ptr x = prim__poke_float_t ptr x

export
fromDouble : CDouble -> CFloat
fromDouble d = unsafePerformIO $ primIO $ prim__double_to_cfloat d

export
toDouble : CFloat -> CDouble
toDouble d = unsafePerformIO $ primIO $ prim__cfloat_to_double d

export
Show CFloat where
  show x = (show $ toDouble x) <+> "f"

export
[FloatNum] Num CFloat where
  a + b = unsafePerformIO $ primIO $ prim__cfloat_add a b
  a * b = unsafePerformIO $ primIO $ prim__cfloat_mul a b
  fromInteger = fromDouble . fromInteger

export
Neg CFloat using FloatNum where
  negate a = unsafePerformIO $ primIO $ prim__cfloat_neg a
  a - b = unsafePerformIO $ primIO $ prim__cfloat_sub a b

export
Fractional CFloat using FloatNum where
  a / b = unsafePerformIO $ primIO $ prim__cfloat_div a b
  recip a = unsafePerformIO $ primIO $ prim__cfloat_recip a

export
Abs CFloat using FloatNum where
  abs a = unsafePerformIO $ primIO $ prim__cfloat_abs a
