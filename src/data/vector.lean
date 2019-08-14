inductive Vector (α : Type) : Nat → Type
| nil {} : Vector 0
| cons {} : ∀ {n : Nat}, α → Vector n → Vector (n + 1)

infixr ` ∷ `:67 := Vector.cons

namespace Vector

variables {n : Nat} {α β : Type}

def head : Vector α (n + 1) → α
| x ∷ xs ⇒ x

def tail : Vector α (n + 1) → Vector α n
| x ∷ xs ⇒ xs

def toList : ∀ {n : Nat}, Vector α n → List α
| 0, Vector.nil ⇒ []
| n + 1, x ∷ xs ⇒ x :: toList xs

end Vector
