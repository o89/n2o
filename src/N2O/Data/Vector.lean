def Vector (α : Type) : Nat → Type
|   0   => Unit
| n + 1 => α × Vector n

namespace Vector

variables {α : Type} {n : Nat}

def nil : Vector α 0 := Unit.unit
def cons : α → Vector α n → Vector α (n + 1) :=
Prod.mk

def head : Vector α (n + 1) → α := Prod.fst
def tail : Vector α (n + 1) → Vector α n := Prod.snd

def toList : ∀ {n : Nat}, Vector α n → List α
|   0,   _       => []
| n + 1, (x, xs) => x :: toList xs

end Vector
