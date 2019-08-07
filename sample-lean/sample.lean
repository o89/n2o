import init.system.io
import Network.N2O.Web.Http Network.N2O.Internal
open Network.N2O.Internal

def handler (socket : WS) : Option String := some (toString socket.toReq.headers)

def main : IO Unit := do
  Network.N2O.Web.Http.setHandler handler;
  Network.N2O.Web.Http.runServer "localhost" 9000
