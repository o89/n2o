import init.system.io
import Network.N2O.Web.Http Network.N2O.Internal
open Network.N2O.Internal

def handler (socket : WS) : IO Unit := do
  IO.println (toString socket.headers);
  IO.println socket.question;
  socket.answer "writing test";
  socket.answer "ping pong"

def main : IO Unit := do
  Network.N2O.Web.Http.setHandler handler;
  Network.N2O.Web.Http.runServer "localhost" 9000
