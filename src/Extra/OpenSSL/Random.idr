module Extra.OpenSSL.Random

import Control.Linear.LIO
import Extra.Bytes
import Extra.FFI
import Extra.OpenSSL.FFI

%foreign libcrypto "RAND_bytes"
export
prim__RAND_bytes : Ptr CUChar -> CInt -> PrimIO CInt

export
rand_bytes : LinearIO io => {size : Nat} -> (1 _ : APtr size) -> L io {use=1} (APtr size)
rand_bytes (MkAPtr ptr) = do
  _ <- liftIO1 $ primIO $ prim__RAND_bytes (castPtr ptr) (cast $ natToInteger size)
  pure1 $ MkAPtr ptr

