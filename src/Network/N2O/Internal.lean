namespace Network.N2O.Internal

def Header := String × String
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

end Network.N2O.Internal
