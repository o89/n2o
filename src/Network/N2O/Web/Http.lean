import init.system.io

namespace Network.N2O.Web.Http

@[extern 2 "lean_set_handler"] constant setHandler (f : (String → IO Unit) → String → Array (String × String) → IO Unit) : IO Unit := default _
@[extern 1 "lean_stop_server"] constant stopServer : IO Unit := default _
@[extern 3 "lean_run_server"] constant runServer (addr : String) (port : UInt16) : IO Unit := default _

end Network.N2O.Web.Http
