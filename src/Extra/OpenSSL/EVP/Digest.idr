module Extra.OpenSSL.EVP.Digest

import Extra.OpenSSL.FFI
import Control.Linear.LIO
import Extra.Bytes
import Extra.FFI

export
data PRIM__EVP_MD : Type where

export
data PRIM__EVP_MD_CTX : Type where

export
data PRIM__ENGINE : Type where

%foreign libcrypto "EVP_sha224"
export
prim__EVP_sha224 : PrimIO (Ptr PRIM__EVP_MD)

%foreign libcrypto "EVP_sha256"
export
prim__EVP_sha256 : PrimIO (Ptr PRIM__EVP_MD)

%foreign libcrypto "EVP_sha384"
export
prim__EVP_sha384 : PrimIO (Ptr PRIM__EVP_MD)

%foreign libcrypto "EVP_sha512"
export
prim__EVP_sha512 : PrimIO (Ptr PRIM__EVP_MD)

%foreign libcrypto "EVP_get_digestbyname"
export
prim__EVP_get_digestbyname : CString -> PrimIO (Ptr PRIM__EVP_MD)

%foreign libcrypto "EVP_MD_CTX_new"
prim__EVP_MD_CTX_new : PrimIO (Ptr PRIM__EVP_MD_CTX)

%foreign libcrypto "EVP_MD_CTX_free"
prim__EVP_MD_CTX_free : Ptr PRIM__EVP_MD_CTX -> PrimIO ()

%foreign libcrypto "EVP_MD_CTX_reset"
prim__EVP_MD_CTX_reset : Ptr PRIM__EVP_MD_CTX -> PrimIO CInt

%foreign libcrypto "EVP_Digest"
export
prim__EVP_Digest : (data_ptr : Ptr CUChar) -> (data_count : SizeT) -> (digest_ret_ptr : Ptr CUChar) -> (digest_size_ret_ptr : Ptr CUInt) -> Ptr PRIM__EVP_MD -> Ptr PRIM__ENGINE -> PrimIO CUInt

%foreign libcrypto "EVP_DigestInit"
export
prim__EVP_DigestInit : Ptr PRIM__EVP_MD_CTX -> Ptr PRIM__EVP_MD -> PrimIO CInt

%foreign libcrypto "EVP_DigestInit_ex"
export
prim__EVP_DigestInit_ex : Ptr PRIM__EVP_MD_CTX -> Ptr PRIM__EVP_MD -> Ptr PRIM__ENGINE -> PrimIO CInt

%foreign libcrypto "EVP_DigestUpdate"
export
prim__EVP_DigestUpdate : Ptr PRIM__EVP_MD_CTX -> Ptr CUChar -> SizeT -> PrimIO CInt

%foreign libcrypto "EVP_DigestFinal_ex"
export
prim__EVP_DigestFinal_ex : Ptr PRIM__EVP_MD_CTX -> Ptr CUChar -> Ptr CUInt -> PrimIO CInt

-- low level abstractions

public export
data HashAlgo : Type where
  Sha224 : HashAlgo
  Sha256 : HashAlgo
  Sha384 : HashAlgo
  Sha512 : HashAlgo
  -- UnknownAlgo : HashAlgo

public export
hashAlgoDigestSize : HashAlgo -> Nat
hashAlgoDigestSize Sha224 = 28
hashAlgoDigestSize Sha256 = 32
hashAlgoDigestSize Sha384 = 48
hashAlgoDigestSize Sha512 = 64

export
data EVP_MD : HashAlgo -> Type where
  MkEVP_MD : Ptr PRIM__EVP_MD -> EVP_MD algo

export
data ENGINE : Type where
  MkENGINE : Ptr PRIM__ENGINE -> ENGINE

export
data EVP_MD_CTX_State : Type where
  EVP_MD_CTX_State_New : EVP_MD_CTX_State
  EVP_MD_CTX_State_Initialized : (algo : HashAlgo) -> EVP_MD_CTX_State
  EVP_MD_CTX_State_Finalized : EVP_MD_CTX_State
  EVP_MD_CTX_State_Freed : EVP_MD_CTX_State

export
data EVP_MD_CTX : EVP_MD_CTX_State -> Type where
  MkEVP_MD_CTX : Ptr PRIM__EVP_MD_CTX -> EVP_MD_CTX state

export
loadEVP_MD : LinearIO io => (algo : HashAlgo) -> L io (EVP_MD algo)
loadEVP_MD Sha224 = liftIO1 (primIO prim__EVP_sha224) >>= \x => pure (MkEVP_MD x)
loadEVP_MD Sha256 = liftIO1 (primIO prim__EVP_sha256) >>= \x => pure (MkEVP_MD x)
loadEVP_MD Sha384 = liftIO1 (primIO prim__EVP_sha384) >>= \x => pure (MkEVP_MD x)
loadEVP_MD Sha512 = liftIO1 (primIO prim__EVP_sha512) >>= \x => pure (MkEVP_MD x)

export
EVP_MD_CTX_new : LinearIO io => L io {use=1} (EVP_MD_CTX EVP_MD_CTX_State_New)
EVP_MD_CTX_new = do
  a <- liftIO1 $ primIO $ prim__EVP_MD_CTX_new
  pure1 $ MkEVP_MD_CTX a

public export
data CanFree_EVP_MD_CTX_State : EVP_MD_CTX_State -> Type where
  CanFree_EVP_MD_CTX_State_New : CanFree_EVP_MD_CTX_State EVP_MD_CTX_State_New
  CanFree_EVP_MD_CTX_State_Initialized : CanFree_EVP_MD_CTX_State (EVP_MD_CTX_State_Initialized _)
  CanFree_EVP_MD_CTX_State_Finalized : CanFree_EVP_MD_CTX_State EVP_MD_CTX_State_Finalized

public export
data CanReset_EVP_MD_CTX_State : EVP_MD_CTX_State -> Type where
  CanReset_EVP_MD_CTX_State_New : CanReset_EVP_MD_CTX_State EVP_MD_CTX_State_New
  CanReset_EVP_MD_CTX_State_Initialized : CanReset_EVP_MD_CTX_State (EVP_MD_CTX_State_Initialized _)
  CanReset_EVP_MD_CTX_State_Finalized : CanReset_EVP_MD_CTX_State EVP_MD_CTX_State_Finalized

public export
data CanInitialize_EVP_MD_CTX_State : EVP_MD_CTX_State -> Type where
  CanInitialize_EVP_MD_CTX_State_New : CanInitialize_EVP_MD_CTX_State EVP_MD_CTX_State_New
  CanInitialize_EVP_MD_CTX_State_Finalized : CanInitialize_EVP_MD_CTX_State EVP_MD_CTX_State_Finalized

export
EVP_MD_CTX_free : LinearIO io => (1 _ : EVP_MD_CTX state) -> {auto okay : CanFree_EVP_MD_CTX_State state} -> L io {use=1} (EVP_MD_CTX EVP_MD_CTX_State_Freed)
EVP_MD_CTX_free (MkEVP_MD_CTX ctx_ptr) = do
  liftIO1 $ primIO $ prim__EVP_MD_CTX_free ctx_ptr
  pure1 $ MkEVP_MD_CTX ctx_ptr

export
doneEVP_MD_CTX : LinearIO io => (1 _ : EVP_MD_CTX EVP_MD_CTX_State_Freed) -> L io ()
doneEVP_MD_CTX (MkEVP_MD_CTX ptr) = pure ()

export
EVP_MD_CTX_reset : LinearIO io => (1 _ : EVP_MD_CTX state) -> {auto okay : CanReset_EVP_MD_CTX_State state} -> L io {use=1} (EVP_MD_CTX EVP_MD_CTX_State_New)
EVP_MD_CTX_reset (MkEVP_MD_CTX ctx_ptr) = do
  _ <- liftIO1 $ primIO $ prim__EVP_MD_CTX_reset ctx_ptr
  pure1 $ MkEVP_MD_CTX ctx_ptr

export
defaultENGINE : ENGINE
defaultENGINE = MkENGINE nullptr

export
EVP_DigestInit_ex : LinearIO io => (1 _ : EVP_MD_CTX state) -> {auto okay : CanInitialize_EVP_MD_CTX_State state} -> EVP_MD algo -> ENGINE -> L io {use=1} (EVP_MD_CTX (EVP_MD_CTX_State_Initialized algo))
EVP_DigestInit_ex (MkEVP_MD_CTX ctx_ptr) (MkEVP_MD md_ptr) (MkENGINE engine_ptr) = do
  _ <- liftIO1 $ primIO $ prim__EVP_DigestInit_ex ctx_ptr md_ptr engine_ptr
  pure1 (MkEVP_MD_CTX ctx_ptr)

export
EVP_DigestUpdate : LinearIO io => (1 _ : EVP_MD_CTX (EVP_MD_CTX_State_Initialized algo)) -> {size : Nat} -> (1 _ : APtr size) -> L io {use=1} (LPair (EVP_MD_CTX (EVP_MD_CTX_State_Initialized algo)) (APtr size))
EVP_DigestUpdate (MkEVP_MD_CTX ctx_ptr) (MkAPtr data_ptr) = do
  let data_count = cast $ natToInteger size
  _ <- liftIO1 $ primIO $ prim__EVP_DigestUpdate ctx_ptr (castPtr data_ptr) data_count
  pure1 $ (MkEVP_MD_CTX ctx_ptr) # (MkAPtr data_ptr)

export
EVP_DigestFinal_ex : LinearIO io => (1 _ : EVP_MD_CTX (EVP_MD_CTX_State_Initialized algo)) -> (1 digest_ret_ptr : APtr (hashAlgoDigestSize algo)) -> L io {use=1} (LPair (EVP_MD_CTX EVP_MD_CTX_State_Finalized) (APtr (hashAlgoDigestSize algo)))
EVP_DigestFinal_ex (MkEVP_MD_CTX ctx_ptr) (MkAPtr digest_ret_ptr) = do
  _ <- liftIO1 $ primIO $ prim__EVP_DigestFinal_ex ctx_ptr (castPtr digest_ret_ptr) nullptr
  pure1 $ (MkEVP_MD_CTX ctx_ptr) # (MkAPtr digest_ret_ptr)

-- TODO: how to determine the true hash algorithm
-- export
-- EVP_get_digestbyname
--   : LinearIO io
--   => (name : APtr size)
--   -> L io (Res Bool (\case
--      False => ()
--      True => (HashAlgo ** EVP_MD algo)
--    ))
