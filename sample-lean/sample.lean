import init.system.io
import Network.N2O.Web.Http
import init.data.array

def main : IO Unit := do
  Network.N2O.Web.Http.setHandler (λ _ f ⇒ none);
  Network.N2O.Web.Http.runServer "localhost" 9000
