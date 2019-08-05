import init.system.io

namespace Network.N2O.Internal

def Header := String × String
instance Header.HasToString : HasToString Header :=
⟨fun pair ⇒ "\"" ++ pair.fst ++ "\" ~ \"" ++ pair.snd ++ "\""⟩

structure Req :=
(path : String)
(method : String)
(version : String)
(headers : List Header)

inductive Result (α : Type)
| reply {} : α → Result
| ok {} : Result
| unknown {} : Result

inductive Event (α : Type)
| init {} : Event
| message {} : α → Event
| terminate {} : Event

structure WS :=
(question : String)
(answer : String → IO Unit)
(headers : Array Header)

end Network.N2O.Internal
