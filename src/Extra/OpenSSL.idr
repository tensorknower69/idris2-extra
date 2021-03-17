module Extra.OpenSSL

import Control.Linear.LIO
import Extra.Bytes
import Extra.FFI

private
libcrypto : String -> String
libcrypto func = "C:" <+> func <+> ",libcrypto"

%foreign libcrypto "RAND_bytes"
private
prim__RAND_bytes : AnyPtr -> CInt -> PrimIO CInt

||| randomize the content of an `APtr`
export
rand_bytes : LinearIO io => {size : Nat} -> (1 _ : APtr size) -> L io {use=1} (APtr size)
rand_bytes (MkAPtr ptr) = do
  _ <- liftIO1 $ primIO $ prim__RAND_bytes ptr (cast $ natToInteger size)
  pure1 $ MkAPtr ptr

private
data EVP_MD : Type where

private
data ENGINE : Type where

%foreign libcrypto "EVP_sha256"
private
prim__EVP_sha256 : PrimIO (Ptr EVP_MD)

%foreign libcrypto "EVP_Digest"
private
prim__EVP_Digest : (data_ptr : AnyPtr) -> (data_count : SizeT) -> (digest_ret_ptr : AnyPtr) -> (digest_size_ret_ptr : Ptr CUInt) -> Ptr EVP_MD -> Ptr ENGINE -> PrimIO CInt

||| One-shot calculates a SHA256 digest
export
sha256 : LinearIO io => {size : Nat} -> (1 _ : APtr size) -> L io {use=1} (LPair (APtr size) (APtr 32))
sha256 (MkAPtr data_ptr) = do
  evp_md <- liftIO1 $ primIO $ prim__EVP_sha256
  let data_count = cast $ natToInteger size
  (MkAPtr digest_ptr) <- allocate 64
  _ <- liftIO1 $ primIO $ prim__EVP_Digest data_ptr data_count digest_ptr nullptr evp_md nullptr
  pure1 (MkAPtr data_ptr # MkAPtr digest_ptr)
