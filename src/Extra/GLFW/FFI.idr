module Extra.GLFW.FFI

import public Extra.C.Types

public export
libglfw : String -> String
libglfw f = "C:" <+> f <+> ",libglfw"
