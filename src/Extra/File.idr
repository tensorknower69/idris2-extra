module Extra.File

import System.File

%foreign "C:fputc,libc"
export
prim__fputc : Int -> FilePtr -> PrimIO Int

export
fputc : HasIO io => Bits8 -> File -> io (Either FileError ())
fputc b (FHandle ptr) = do
  let c = cast b
  c' <- primIO $ prim__fputc c ptr
  pure $ if c' == c then Right () else Left FileWriteError
