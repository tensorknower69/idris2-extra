module Extra.C.FFI

public export
libc : String -> String
libc f = "C:" <+> f <+> ",libc"

public export
libextra : String -> String
libextra f = "C:" <+> f <+> ",libextra"
