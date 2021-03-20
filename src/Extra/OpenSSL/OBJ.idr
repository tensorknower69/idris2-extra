module Extra.OpenSSL.OBJ

import Control.Linear.LIO
import Extra.C.CPtr
import Extra.OpenSSL.FFI
import public Extra.OpenSSL.OBJData

%foreign libcrypto "OBJ_nid2sn"
export
prim__OBJ_nid2sn : CInt -> PrimIO CString

export
OBJ_nid2sn : LinearIO io => NID -> L io (CPtr (NullTerminated False))
OBJ_nid2sn (MkNID id) = do
  ptr <- primIO $ prim__OBJ_nid2sn id
  pure $ MkCPtr ptr
