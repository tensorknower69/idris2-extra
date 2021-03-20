module Extra.OpenSSL.Random

import Control.Linear.LIO
import Extra.OpenSSL.FFI
import Extra.C.CPtr

%foreign libcrypto "RAND_bytes"
export
prim__RAND_bytes : Ptr CUInt8 -> CInt -> PrimIO CInt

export
RAND_bytes
  : LinearIO io
  => {length : Nat}
  -> (1 _ : CPtr (Bytes can_free True can_write length))
  -> L io {use=1} (CPtr (Bytes can_free can_write can_write length))
RAND_bytes (MkCPtr ptr) = do
  _ <- liftIO1 $ primIO $ prim__RAND_bytes ptr (cast $ natToInteger length)
  pure1 $ MkCPtr ptr
