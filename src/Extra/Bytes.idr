module Extra.Bytes

import Data.Nat
import Extra.FFI
import Extra.Proof
import public Control.Linear.LIO
import public Data.Fin
import public Data.Vect
import public Extra.Pair

-- TODO: provide optimized functions, like use Int instead of Nat
public export
interface ByteAccess (f : Nat -> Type) where
  -- TODO: add withAllocate, sometimes not having enough memory is an issue
  allocate : LinearIO io => (size : Nat) -> L io {use=1} (f size)
  free : LinearIO io => (1 _ : f size) -> L io ()

  setBits8 : LinearIO io => (index : Fin size) -> Bits8 -> (1 _ : f size) -> L io {use=1} (f size)
  getBits8 : LinearIO io => (index : Fin size) -> (1 _ : f size) -> L io {use=1} (LLPair (f size) Bits8)

  -- TODO: how do i rewrite linear values?
  setBits8s : LinearIO io => {a, b : Nat} -> Fin (S b) -> Vect a Bits8 -> (1 _ : f (a + b)) -> L io {use=1} (f (a + b))
  setBits8s {a = Z} _ Nil mem = pure1 mem
  setBits8s {a = S len} pos (bits8 :: bits8s) mem = do
    mem <- Extra.Bytes.setBits8 (weakenN len pos) bits8 (replace1 {p = f . S} (plusCommutative len b) mem)
    mem <- setBits8s (FS pos) bits8s (replace1 {p = f} (plusCommutative (S b) len) mem)
    pure1 $ replace1 {p = f} (sym $ plusSuccRightSucc len b) mem

  -- TODO: how do i rewrite linear values?
  getBits8s : LinearIO io => {b : Nat} -> Fin (S b) -> (a : Nat) -> (1 _ : f (a + b)) -> L io {use=1} (LLPair (f (a + b)) (Vect a Bits8))
  getBits8s _ Z mem = pure1 $ mem # Nil
  getBits8s pos (S n) mem = do
    (mem # bits8) <- Extra.Bytes.getBits8 (weakenN n pos) (replace1 {p = f . S} (plusCommutative n b) mem)
    (mem # bits8s) <- Extra.Bytes.getBits8s (FS pos) n (replace1 {p = f} (plusCommutative (S b) n) mem)
    pure1 $ replace1 {p = f} (sym $ plusSuccRightSucc n b) mem # (bits8 :: bits8s)

  pack : LinearIO io => {size : Nat} -> Vect size Bits8 -> L io {use=1} (f size)
  pack bits8s = do
    mem <- allocate size
    mem <- setBits8s {b = 0} FZ bits8s (replace1 {p = f} (sym $ plusZeroRightNeutral size) mem)
    pure1 $ (replace1 {p = f} (plusZeroRightNeutral size) mem)

  unpack : LinearIO io => {size : Nat} -> (1 _ : f size) -> L io {use=1} (LLPair (f size) (Vect size Bits8))
  unpack mem = do
    (mem # bits8s) <- getBits8s {b = 0} FZ size (replace1 {p = f} (sym $ plusZeroRightNeutral size) mem)
    pure1 $ (replace1 {p = f} (plusZeroRightNeutral size) mem) # bits8s

public export
data APtr : Nat -> Type where
  MkAPtr : (ptr : AnyPtr) -> APtr size

export
%foreign "C:malloc,libc"
prim__malloc : SizeT -> PrimIO AnyPtr

export
%foreign "C:free,libc"
prim__free : AnyPtr -> PrimIO ()

export
%foreign "C:peek,libextra"
prim__peek : AnyPtr -> SizeT -> PrimIO Bits8

export
%foreign "C:poke,libextra"
prim__poke : AnyPtr -> SizeT -> Bits8 -> PrimIO ()

export
ByteAccess APtr where
  allocate size = do
    ptr <- liftIO1 $ primIO $ prim__malloc (cast $ natToInteger size)
    pure1 $ MkAPtr ptr

  free (MkAPtr ptr) = liftIO1 $ primIO $ prim__free ptr

  getBits8 pos (MkAPtr ptr) = do
    bits8 <- liftIO1 $ primIO $ prim__peek ptr (cast $ finToInteger pos)
    pure1 $ MkAPtr ptr # bits8

  setBits8 pos bits8 (MkAPtr ptr) = do
    liftIO1 $ primIO $ prim__poke ptr (cast $ finToInteger pos) bits8
    pure1 $ MkAPtr ptr
