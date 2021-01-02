import N2O.Network.Internal

@[extern 2 "lean_set_handler"] constant setHandler (handler : WS → Result) : IO Unit
@[extern 1 "lean_stop_server"] constant stopServer : IO Unit
@[extern 3 "lean_run_server"] constant runServer (addr : String) (port : UInt16) : IO Unit

def canonicalHandler (handler : Handler) (socket : WS) : Result :=
handler socket.toReq socket.question

def startServer (handler : Handler) (addr : String × UInt16) : IO Unit :=
do setHandler (canonicalHandler handler); runServer addr.fst addr.snd
