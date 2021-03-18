module Extra.OpenSSL.FFI

public export
libcrypto : String -> String
libcrypto func = "C:" <+> func <+> ",libcrypto"
