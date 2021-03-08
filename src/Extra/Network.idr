module Extra.Network

import Control.Linear.LIO
import Extra.Bytes
import Extra.FFI
import Extra.Proof
import Network.Socket
import Network.Socket.Raw
import public Network.Socket.Data

export
%foreign "C:send,libc"
prim__socket_send : SocketDescriptor -> (ptr : AnyPtr) -> (nbytes : SizeT) -> (flags : Bits32) -> PrimIO SSizeT

export
%foreign "C:recv,libc"
prim__socket_recv : SocketDescriptor -> (ptr : AnyPtr) -> (nbytes : SizeT) -> (flags : Bits32) -> PrimIO SSizeT

export
socket_send : HasIO io => Socket.Data.Socket -> AnyPtr -> SizeT -> io SSizeT
socket_send sock ptr nbytes = do
  ret <- primIO $ prim__socket_send sock.descriptor ptr nbytes 0
  pure ret

export
socket_recv : HasIO io => Socket.Data.Socket -> AnyPtr -> SizeT -> io SSizeT
socket_recv sock ptr nbytes = do
  ret <- primIO $ prim__socket_recv sock.descriptor ptr nbytes 0
  pure ret

public export
data SocketState = Ready | Bound | Listening | Open | Closed
public export
data CanConnect : SocketState -> Type where
  CanConnect_Ready : CanConnect Ready
  CanConnect_Bound : CanConnect Bound

public export
data Protocol : Type where
  TCP : Protocol
  UDP : Protocol
  Default : Protocol

export
protocolNumber : Protocol -> ProtocolNumber
protocolNumber Default = 0
protocolNumber TCP = 6
protocolNumber UDP = 17

export
data Socket : SocketFamily -> SocketType -> Protocol -> SocketState -> Type where
     MkSocket : Socket.Data.Socket -> Socket family type protocol state

export
newSocket :
  LinearIO io
  => (family  : SocketFamily)
  -> (type : SocketType)
  -> (protocol : Protocol)
  -> (success : (1 _ : Socket family type protocol Ready) -> L io ())
  -> (fail : SocketError -> L io ())
  -> L io ()
newSocket family type protocol on_success on_fail = do
  Right sock <- socket family type (protocolNumber protocol)
    | Left err => on_fail err
  on_success (MkSocket sock)

export
close : LinearIO io => (1 _ : Socket family type protocol state) -> L io {use=1} (Socket family type protocol Closed)
close (MkSocket sock) = do
  Socket.close sock
  pure1 (MkSocket sock)

export
done : LinearIO io => (1 _ : Socket family type protocol Closed) -> L io ()
done (MkSocket sock) = pure ()

export
bind :
  LinearIO io
  => (1 _ : Socket family type protocol Ready)
  -> (addr : Maybe SocketAddress)
  -> (port : Port)
  -> L io {use=1} (Res Bool (\res => Socket family type protocol (case res of {False => Closed; True => Bound})))
bind (MkSocket sock) addr port = do
  ok <- Socket.bind sock addr port
  pure1 $ ok == 0 # MkSocket sock

export
connect :
  LinearIO io
  => (1 _ : Socket family type protocol state)
  -> {auto 0 can_connect : CanConnect state}
  -> (addr : SocketAddress)
  -> (port : Port)
  -> L io {use=1} (Res Bool (\res => Socket family type protocol (case res of {False => Closed; True => Open})))
connect (MkSocket sock) addr port = do
  ok <- Socket.connect sock addr port
  pure1 $ ok == 0 # MkSocket sock

export
listen :
  LinearIO io
  => (1 _ : Socket family type protocol Bound)
  -> L io {use=1} (Res Bool (\res => Socket family type protocol (case res of {False => Closed; True => Listening})))
listen (MkSocket sock) = do
  ok <- Socket.listen sock
  pure1 $ ok == 0 # MkSocket sock

export
accept :
  LinearIO io
  => (1 _ : Socket family type protocol Listening)
  -> L io {use=1} (Res Bool (\case
    False => Socket family type protocol Listening
    True => (LPair (Socket family type protocol Listening) (Socket family type protocol Open))))
accept (MkSocket sock) = do
  Right (sock', sockaddr) <- Socket.accept sock
    | Left err => pure1 (False # (MkSocket sock))
  pure1 $ True # (MkSocket sock # MkSocket sock')

export
data SockBuf : (size : Nat) -> Type where
  MkSockBuf : (bptr : BufPtr) -> SockBuf size

export
implementation ByteAccess SockBuf where
  allocate size = do
    bptr <- liftIO1 $ sock_alloc (cast $ natToInteger size)
    pure1 $ MkSockBuf bptr

  free (MkSockBuf bptr) = liftIO1 $ sock_free bptr

  setBits8 index bits8 (MkSockBuf bptr) = do
    let offset = cast {to = Int} $ finToInteger index
    let int = cast {to = Int} bits8
    liftIO1 $ sock_poke bptr offset int
    pure1 $ MkSockBuf bptr

  getBits8 index (MkSockBuf bptr) = do
    int <- liftIO1 $ sock_peek bptr (cast $ finToInteger index)
    let bits8 = cast {to = Bits8} int
    pure1 $ MkSockBuf bptr # bits8

export
send : (LinearIO io)
  => (1 sock : Socket family type protocol Open)
  -> {size : Nat}
  -> (1 _ : APtr size)
  -> L io {use=1} (Res (APtr size, Bool) (\(_, bool) => Socket family type protocol (case bool of {False => Closed; True => Open})))
send (MkSocket sock) (MkAPtr ptr) = do
  _ <- liftIO1 $ socket_send sock ptr (cast $ natToInteger size)
  pure1 ((MkAPtr ptr, True) # MkSocket sock)

-- TODO: optimize
export
recv
  : LinearIO io
  => (1 _ : Socket family type protocol Open)
  -> (max_size : Nat)
  -> L io {use=1} (Res (Maybe Nat) (\res =>
       case res of
         Nothing => Socket family type protocol Closed
         Just size => LPair (Socket family type protocol Open) (APtr size)
       )
     )
recv (MkSocket sock) max_size = do
  MkAPtr ptr <- allocate max_size
  size <- socket_recv sock ptr (cast $ natToInteger max_size)
  let size = integerToNat (cast size)
  pure1 $ (Just size) # (MkSocket sock # MkAPtr ptr)

-- TODO: implement udp stuff

-- export
-- recvAll : LinearIO io =>
--           (1 _ : Socket Open) ->
--           L io {use=1} (Res (Maybe String)
--                             (\res => Socket (case res of
--                                                   Nothing => Closed
--                                                   Just msg => Open)))
-- recvAll (MkSocket sock)
--     = do Right msg <- Socket.recvAll sock
--              | Left err => pure1 (Nothing # MkSocket sock)
--          pure1 (Just msg # MkSocket sock)

-- recv : LinearIO io
--   => Socket family type protocol Open
--   -> Buffer
--   -> ByteLength
--   -> (on_fail    : (Socket family type protocol Closed) -> L io {use=1} ())
--   -> (on_success : (Socket family type protocol Open  ) -> L io () )
-- recv sock buf len = do
--   ptr <- sock_alloc len
--   recvBuf sock ptr len
