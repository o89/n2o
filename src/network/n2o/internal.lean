import init.system.io

def String.init (s : String) := s.extract 0 (s.length - 1)

namespace network.n2o.internal

def Header := String × String
instance Header.HasToString : HasToString Header :=
⟨fun pair ⇒ pair.fst ++ ": " ++ pair.snd⟩

inductive Msg
| text : String → Msg
| binary : Array UInt8 → Msg

instance : HasToString Msg :=
⟨λ m ⇒ match m with
  | Msg.text str ⇒ str
  | Msg.binary lst ⇒ toString lst⟩

structure Req :=
(path : String)
(method : String)
(version : String)
(headers : List Header)

inductive Result
| error {} : String → Result
| warning {} : String → Result
| reply {} : Msg → Result
| ok {} : Result

def Handler := Req → Msg → Result

structure Proto :=
(prot : Type) -- Input type for protocol handler
(ev : Type) -- Output type for protocol handler and input type for event handler
(res req : Type)
(nothing : res)
(proto : prot → ev)

structure Cx (m : Proto) :=
(req : m.req) (module : m.ev → m.res)

def Context.run (m : Proto) (cx : Cx m)
  (handlers : List (Cx m → Cx m)) (msg : m.prot) :=
(handlers.foldl (λ x (f : Cx m → Cx m) ⇒ f x) cx).module (m.proto msg)

def mkHandler (m : Proto) (handlers : List (Cx m → Cx m)) : m.req → m.prot → m.res :=
λ req msg ⇒ Context.run m ⟨req, λ _ ⇒ m.nothing⟩ handlers msg

structure WS :=
(question : Msg)
(headers : Array (String × String))

def Header.dropBack : Header → Option Header
| (name, value) ⇒
  if name.back = ':' then some (name.init, value)
  else none

def Header.isHeader : String → Bool
| "get "    ⇒ true
| "post "   ⇒ true
| "option " ⇒ true
| _         ⇒ false

def WS.toReq (socket : WS) : Req :=
let headersList := socket.headers.toList;
let headers := List.filterMap Header.dropBack headersList;
{ path := Option.getOrElse
            (headersList.lookup "get " <|>
             headersList.lookup "post " <|>
             headersList.lookup "option ") "",
  method := Option.getOrElse
              (String.trimRight <$> Prod.fst <$>
                headersList.find (Header.isHeader ∘ Prod.fst)) "",
  version := Option.getOrElse
               (Prod.snd <$> headersList.find
                 (String.isPrefixOf "http" ∘ Prod.fst)) "",
  headers := headers }

end network.n2o.internal
