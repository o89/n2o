import Network.N2O.Internal
open Network.N2O.Internal

namespace Network.N2O.Web.Http

@[extern 2 "lean_set_handler"] constant setHandler (handler : @& WS → IO Unit) : IO Unit := default _
@[extern 1 "lean_stop_server"] constant stopServer : IO Unit := default _
@[extern 3 "lean_run_server"] constant runServer (addr : String) (port : UInt16) : IO Unit := default _

end Network.N2O.Web.Http
