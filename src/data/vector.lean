inductive Vector (α : Type) : Nat → Type
| nil {} : Vector 0
| cons {} : ∀ {n : Nat}, α → Vector n → Vector (n + 1)

infixr ` ∷ `:67 := Vector.cons

namespace Vector

variables {n : Nat} {α : Type}

def head : Vector α (n + 1) → α
| x ∷ xs ⇒ x

def tail : Vector α (n + 1) → Vector α n
| x ∷ xs ⇒ xs

end Vector
