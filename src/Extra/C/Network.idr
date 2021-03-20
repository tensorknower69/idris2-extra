||| A replacement for Control.Linear.Network and use `Ptr`s instead of `String`s
module Extra.C.Network

import Control.Linear.LIO
import Extra.C.CPtr
import Extra.Proof
import Data.Nat
import Network.Socket
import Network.Socket.Raw
import public Network.Socket.Data

||| libc `send` in idris2
export
%foreign "C:send,libc"
prim__socket_send : SocketDescriptor -> (ptr : Ptr CUInt8) -> (nbytes : SizeT) -> (flags : Bits32) -> PrimIO SSizeT

||| libc `recv` in idris2
export
%foreign "C:recv,libc"
prim__socket_recv : SocketDescriptor -> (ptr : Ptr CUInt8) -> (nbytes : SizeT) -> (flags : Bits32) -> PrimIO SSizeT

||| `prim__socket_send` with higher level primitives in idris2
export
socket_send : HasIO io => Socket.Data.Socket -> (data_ptr : Ptr CUInt8) -> (data_size : SizeT) -> io SSizeT
socket_send sock ptr nbytes = do
  ret <- primIO $ prim__socket_send sock.descriptor ptr nbytes 0
  pure ret

||| `prim__socket_recv` with higher level primitives in idris2
export
socket_recv : HasIO io => Socket.Data.Socket -> (data_ret_ptr : Ptr CUInt8) -> SizeT -> io SSizeT
socket_recv sock ptr nbytes = do
  ret <- primIO $ prim__socket_recv sock.descriptor ptr nbytes 0
  pure ret

||| Assumed states of a socket. Keep in mind that unintentional tempering can fundamentally destroy the premise
public export
data SocketState = Ready | Bound | Listening | Open | Closed

||| Used to specify which states enables the socket be called with `connect`
public export
data CanConnect : SocketState -> Type where
  CanConnect_Ready : CanConnect Ready
  CanConnect_Bound : CanConnect Bound

||| Possible protocols of a socket, usually you use `Default`
public export
data Protocol : Type where
  TCP : Protocol
  UDP : Protocol
  Default : Protocol

||| An auxiliary function to convert Protocol into its corresponding magic number
export
protocolNumber : Protocol -> ProtocolNumber
protocolNumber Default = 0
protocolNumber TCP = 6
protocolNumber UDP = 17

||| The `Socket`, I don't expose the constructor in order to prevent incorrect usages
export
data Socket : SocketFamily -> SocketType -> Protocol -> SocketState -> Type where
     MkSocket : Socket.Data.Socket -> Socket family type protocol state

||| Construct a socket
export
newSocket
  : LinearIO io
  => (family  : SocketFamily)
  -> (type : SocketType)
  -> (protocol : Protocol)
  -> L io {use=1}
    ( Res (Maybe SocketError) (\case
      Just err => ()
      Nothing  => Socket family type protocol Ready
    ))
newSocket family type protocol = do
  Right sock <- socket family type (protocolNumber protocol)
    | Left err => pure1 $ Just err # ()
  pure1 $ Nothing # (MkSocket sock)

||| Close a socket, you may want to call `done` too to kill the socket
export
close : LinearIO io => (1 _ : Socket family type protocol state) -> L io {use=1} (Socket family type protocol Closed)
close (MkSocket sock) = do
  Socket.close sock
  pure1 (MkSocket sock)

||| Finish a socket
export
done : LinearIO io => (1 _ : Socket family type protocol Closed) -> L io ()
done (MkSocket sock) = pure ()

||| Bind a socket
export
bind
  : LinearIO io
  => (1 _ : Socket family type protocol Ready)
  -> (addr : Maybe SocketAddress)
  -> (port : Port)
  -> L io {use=1} (Res Bool (\res => Socket family type protocol (case res of {False => Closed; True => Bound})))
bind (MkSocket sock) addr port = do
  ok <- Socket.bind sock addr port
  pure1 $ ok == 0 # MkSocket sock

||| Connect a socket to an address
export
connect
  : LinearIO io
  => (1 _ : Socket family type protocol state)
  -> {auto 0 can_connect : CanConnect state}
  -> (addr : SocketAddress)
  -> (port : Port)
  -> L io {use=1} (Res Bool (\res => Socket family type protocol (case res of {False => Closed; True => Open})))
connect (MkSocket sock) addr port = do
  ok <- Socket.connect sock addr port
  pure1 $ ok == 0 # MkSocket sock

||| Put a socket into listen mode
export
listen :
  LinearIO io
  => (1 _ : Socket family type protocol Bound)
  -> L io {use=1} (Res Bool (\res => Socket family type protocol (case res of {False => Closed; True => Listening})))
listen (MkSocket sock) = do
  ok <- Socket.listen sock
  pure1 $ ok == 0 # MkSocket sock

||| Put a socket into accept mode and blocks until a client connects to it
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

-- TODO: handle return error
||| Send some data via a socket
export
send : (LinearIO io)
  => (1 sock : Socket family type protocol Open)
  -> {length : Nat}
  -> (1 _ : CPtr (Bytes can_free True can_write length))
  -> L io {use=1}
      ( LPair
        ( CPtr (Bytes can_free True can_write length)
        )
        ( Res Bool
          ( \case
            False => Socket family type protocol Closed
            True  => Socket family type protocol Open
          )
        ) 
      )
send (MkSocket sock) (MkCPtr ptr) = do
  _ <- liftIO1 $ socket_send sock ptr (cast $ natToInteger length)
  pure1 $ MkCPtr ptr # (True # MkSocket sock)

-- TODO: handle return error
||| Receive some data from a socket
export
recv
  : LinearIO io
  => (1 _ : Socket family type protocol Open)
  -> {max_length : Nat}
  -> (1 _ : CPtr (Bytes can_free can_read True max_length))
  -> L io {use=1}
       ( LPair
         ( CPtr (Bytes can_free can_read True max_length) )
         ( Res (Maybe (DPair Nat (\length => LTE length max_length))) ( \case
           Nothing => Socket family type protocol Closed
           Just _  => Socket family type protocol Open
         ))
       )
recv (MkSocket sock) (MkCPtr ptr) = do
  length <- socket_recv sock ptr (cast $ natToInteger max_length)
  let length = integerToNat (cast length)
  let cptr = MkCPtr ptr
  pure1 $ cptr # (Just (length ** believe_me ()) # MkSocket sock)

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
