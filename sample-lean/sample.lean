import init.system.io
import Network.N2O.Web.Http
import init.data.array

def handler (write : String → IO Unit) (input : String)
  (f : Array (String × String)) : IO Unit := do
  IO.println (toString f);
  write "1";
  write "2"

def main : IO Unit := do
  Network.N2O.Web.Http.setHandler handler;
  Network.N2O.Web.Http.runServer "localhost" 9000
