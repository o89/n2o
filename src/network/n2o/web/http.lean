import network.n2o.internal
open network.n2o.internal

namespace network.n2o.web.http

@[extern 2 "lean_set_handler"] constant setHandler (handler : WS → Result) : IO Unit := default _
@[extern 1 "lean_stop_server"] constant stopServer : IO Unit := default _
@[extern 3 "lean_run_server"] constant runServer (addr : String) (port : UInt16) : IO Unit := default _

def canonicalHandler (handler : Handler) (socket : WS) : Result :=
handler socket.toReq socket.question

def startServer (handler : Handler) (addr : String × UInt16) := do
setHandler (canonicalHandler handler); runServer addr.fst addr.snd

end network.n2o.web.http
