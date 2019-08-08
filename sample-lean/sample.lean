import init.system.io
import Network.N2O.Web.Http Network.N2O.Internal
open Network.N2O.Internal

def handler (req : Req) (msg : Msg) : Result := Result.reply msg

def main := Network.N2O.Web.Http.startServer handler ("localhost", 9000)
