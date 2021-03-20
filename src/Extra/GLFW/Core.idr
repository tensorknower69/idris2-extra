module Extra.GLFW.Core

import Extra.GLFW.FFI
import public Extra.C.Types
import Control.Linear.LIO

%foreign libglfw "glfwInit"
export
prim__glfwInit : PrimIO CInt

%foreign libglfw "glfwTerminate"
export
prim__glfwTerminate : PrimIO ()

%foreign libglfw "glfwGetVersion"
export
prim__glfwGetVersion : Ptr CInt -> Ptr CInt -> Ptr CInt -> PrimIO ()

export
data GLFWmonitor : Type where

export
data GLFWwindow : Type where

%foreign libglfw "glfwCreateWindow"
export
prim__glfwCreateWindow : CInt -> CInt -> CString -> Ptr GLFWmonitor -> Ptr GLFWwindow -> PrimIO (Ptr GLFWwindow)

%foreign libglfw "glfwWindowShouldClose"
export
prim__glfwWindowShouldClose : Ptr GLFWwindow -> PrimIO CInt

%foreign libglfw "glfwSetWindowShouldClose"
export
prim__glfwSetWindowShouldClose : Ptr GLFWwindow -> CInt -> PrimIO ()

%foreign libglfw "glfwSwapBuffers"
export
prim__glfwSwapBuffers : Ptr GLFWwindow -> PrimIO ()

%foreign libglfw "glfwPollEvents"
export
prim__glfwPollEvents : PrimIO ()
