import init.system.io
import network.n2o.web.http network.n2o.internal
open network.n2o.web.http network.n2o.internal

def echoProto : Proto :=
{ prot := Msg,
  ev := Option String,
  res := Result,
  req := Req,
  nothing := Result.ok,
  proto := λ p ⇒ match p with
    | Msg.text s ⇒ some s
    | _ ⇒ none }

def echo : echoProto.ev → echoProto.res
| none := Result.ok
| (some s) := Result.reply (Msg.text s)

def router (cx : Cx echoProto) : Cx echoProto :=
⟨cx.req, echo⟩

def handler : Handler := mkHandler echoProto [ router ]
def main := startServer handler ("localhost", 9000)