import init.system.io
import network.n2o.web.http network.n2o.internal
open network.n2o.web.http network.n2o.internal

def handler (req : Req) (msg : Msg) : Result := Result.reply msg

def main := startServer handler ("localhost", 9000)
