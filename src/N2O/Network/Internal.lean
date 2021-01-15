import Init.System.IO

def String.init (s : String) := s.extract 0 (s.length - 1)

def Header := String × String
instance Header.ToString : ToString Header :=
⟨fun pair => pair.fst ++ ": " ++ pair.snd⟩

inductive Msg
| text   : String → Msg
| binary : ByteArray → Msg

instance : ToString Msg :=
⟨λ m => match m with
  | Msg.text str => str
  | Msg.binary lst => toString lst⟩

structure Req :=
(path    : String)
(method  : String)
(version : String)
(headers : List Header)

inductive Result
| error {}   : String → Result
| warning {} : String → Result
| reply {}   : Msg → Result
| ok {}      : Result

def Handler := Req → Msg → Result

structure Proto :=
(ev      : Type) -- Output type for protocol handler and input type for event handler
(nothing : Result)
(proto   : Msg → ev)

structure Cx (m : Proto) :=
(req : Req) (module : m.ev → Result)

def Context.run (m : Proto) (cx : Cx m)
  (handlers : List (Cx m → Cx m)) (msg : Msg) :=
(handlers.foldl (λ x (f : Cx m → Cx m) => f x) cx).module (m.proto msg)

def uselessRouter (m : Proto) : m.ev → Result :=
λ _ => m.nothing

def mkHandler (m : Proto) (handlers : List (Cx m → Cx m)) : Handler :=
λ req msg => Context.run m ⟨req, uselessRouter m⟩ handlers msg

structure WS :=
(question : Msg)
(headers  : Array (String × String))

def Header.dropBack : Header → Option Header
| (name, value) =>
  if name.back = ':' then some (name.init, value)
  else none

def Header.isHeader : String → Bool
| "get "    => true
| "post "   => true
| "option " => true
| _         => false

def WS.toReq (socket : WS) : Req :=
let headersList := socket.headers.toList;
let headers := List.filterMap Header.dropBack headersList;
{ path := Option.getD
            (headersList.lookup "get " <|>
             headersList.lookup "post " <|>
             headersList.lookup "option ") "",
  method := Option.getD
              (String.trimRight <$> Prod.fst <$>
                headersList.find? (Header.isHeader ∘ Prod.fst)) "",
  version := Option.getD
               (Prod.snd <$> headersList.find?
                 (String.isPrefixOf "http" ∘ Prod.fst)) "",
  headers := headers }
