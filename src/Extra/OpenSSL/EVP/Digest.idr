module Extra.OpenSSL.EVP.Digest

import Control.Linear.LIO
import Extra.C.CPtr
import Extra.C.Ptr
import Extra.OpenSSL.FFI
import Extra.OpenSSL.OBJ

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

%foreign libcrypto "EVP_MD_type"
export
prim__EVP_MD_type : Ptr PRIM__EVP_MD -> PrimIO CInt

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
  Sha1 : HashAlgo
  Sha224 : HashAlgo
  Sha256 : HashAlgo
  Sha384 : HashAlgo
  Sha512 : HashAlgo
  Md4 : HashAlgo
  Md5 : HashAlgo
  -- UnknownAlgo : HashAlgo

public export
nidToHashAlgo : NID -> Maybe HashAlgo
nidToHashAlgo (MkNID 64)  = Just Sha1
nidToHashAlgo (MkNID 675) = Just Sha224
nidToHashAlgo (MkNID 672) = Just Sha256
nidToHashAlgo (MkNID 673) = Just Sha384
nidToHashAlgo (MkNID 674) = Just Sha512
nidToHashAlgo (MkNID 257) = Just Md4
nidToHashAlgo (MkNID 4) = Just Md5
nidToHashAlgo _ = Nothing

public export
hashAlgoDigestSize : HashAlgo -> Nat
hashAlgoDigestSize Sha1   = 20
hashAlgoDigestSize Sha224 = 28
hashAlgoDigestSize Sha256 = 32
hashAlgoDigestSize Sha384 = 48
hashAlgoDigestSize Sha512 = 64
hashAlgoDigestSize Md4    = 16
hashAlgoDigestSize Md5    = 16

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
EVP_DigestUpdate
  : LinearIO io
  => (1 _ : EVP_MD_CTX (EVP_MD_CTX_State_Initialized algo))
  -> {length : Nat}
  -> (1 _ : CPtr (Bytes can_free True can_write length))
  -> L io {use=1} (LPair (EVP_MD_CTX (EVP_MD_CTX_State_Initialized algo)) (CPtr (Bytes can_free True can_write length)))
EVP_DigestUpdate (MkEVP_MD_CTX ctx_ptr) (MkCPtr data_ptr) = do
  let data_count = cast $ natToInteger length
  _ <- liftIO1 $ primIO $ prim__EVP_DigestUpdate ctx_ptr data_ptr data_count
  pure1 $ (MkEVP_MD_CTX ctx_ptr) # (MkCPtr data_ptr)

export
EVP_DigestFinal_ex
  : LinearIO io
  => (1 _ : EVP_MD_CTX (EVP_MD_CTX_State_Initialized algo))
  -> (1 digest_ret_ptr : CPtr (Bytes can_free can_read True (hashAlgoDigestSize algo)))
  -> L io {use=1} (LPair (EVP_MD_CTX EVP_MD_CTX_State_Finalized) (CPtr (Bytes can_free can_read True (hashAlgoDigestSize algo))))
EVP_DigestFinal_ex (MkEVP_MD_CTX ctx_ptr) (MkCPtr digest_ret_ptr) = do
  _ <- liftIO1 $ primIO $ prim__EVP_DigestFinal_ex ctx_ptr digest_ret_ptr nullptr
  pure1 $ (MkEVP_MD_CTX ctx_ptr) # (MkCPtr digest_ret_ptr)

public export
data ExDigestByName : Type where
  NotImplementedYet : ExDigestByName
  NotFound : ExDigestByName

export
Show ExDigestByName where
  show NotImplementedYet = "not implemented yet"
  show NotFound = "not found"

export
EVP_get_digestbyname
  : LinearIO io
  => (1 name : CPtr (NullTerminated can_free))
  -> L io {use=1} (Res Bool (\case
     False => Res ExDigestByName (\_ => CPtr (NullTerminated can_free))
     True  => Res (DPair HashAlgo EVP_MD) (\_ => CPtr (NullTerminated can_free))
   ))
EVP_get_digestbyname (MkCPtr name_ptr) = do
  md_ptr <- primIO $ prim__EVP_get_digestbyname name_ptr
  case md_ptr == nullptr of
    True => pure1 $ False # (NotFound # MkCPtr name_ptr)
    False => do
      id_ <- primIO $ prim__EVP_MD_type md_ptr
      printLn id_
      pure1 $ case nidToHashAlgo (MkNID id_) of
        Nothing => False # (NotImplementedYet # MkCPtr name_ptr)
        Just algo => True # ((algo ** MkEVP_MD md_ptr) # MkCPtr name_ptr)
