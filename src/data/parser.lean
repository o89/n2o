-- data.buffer.parser from Lean 3 stdlib

import data.vector

inductive ParseResult (α : Type)
| done (pos : Nat) (result : α) : ParseResult
| fail (pos : Nat) (msg : List String) : ParseResult

class BuiltFrom (Γ : Type) (π : Type) :=
(size {} : Γ → Nat)
(eq {} : π → π → Bool)
(get {} : Γ → Nat → π)

def Parser (Γ π : Type) [BuiltFrom Γ π] (α : Type) :=
∀ (input : Γ) (start : Nat), ParseResult α

instance : BuiltFrom ByteArray UInt8 :=
{ size := ByteArray.size,
  eq := HasBeq.beq,
  get := ByteArray.get }

abbrev ByteParser := Parser ByteArray UInt8

namespace Parser
variables {Γ π : Type} [BuiltFrom Γ π] {α β : Type}

protected def bind (p : Parser Γ π α) (f : α → Parser Γ π β) : Parser Γ π β :=
λ input pos ⇒ match p input pos with
| ParseResult.done pos a ⇒ f a input pos
| ParseResult.fail _ pos msg ⇒ ParseResult.fail β pos msg

protected def pure (a : α) : Parser Γ π α :=
λ input pos ⇒ ParseResult.done pos a

protected def fail (msg : String) : Parser Γ π α :=
λ _ pos ⇒ ParseResult.fail α pos [ msg ]

instance : Monad (Parser Γ π) :=
{ pure := @Parser.pure Γ π _,
  bind := @Parser.bind Γ π _ }

instance : MonadFail (Parser Γ π) :=
{ fail := @Parser.fail Γ π _ }

protected def failure : Parser Γ π α :=
λ _ pos ⇒ ParseResult.fail α pos []

protected def orelse (p q : Parser Γ π α) : Parser Γ π α :=
λ input pos ⇒ match p input pos with
| ParseResult.fail _ pos₁ msg₁ ⇒
  if pos₁ ≠ pos then ParseResult.fail _ pos₁ msg₁
  else match q input pos with
  | ParseResult.fail _ pos₂ msg₂ ⇒
    if pos₁ < pos₂ then ParseResult.fail _ pos₁ msg₁
    else if pos₂ < pos₁ then ParseResult.fail _ pos₂ msg₂
    else ParseResult.fail _ pos₁ (msg₁ ++ msg₂)
  | ok ⇒ ok
| ok ⇒ ok

instance : Alternative (Parser Γ π) :=
{ failure := @Parser.failure Γ π _,
  orelse := @Parser.orelse Γ π _ }

instance : Inhabited (Parser Γ π α) := ⟨failure⟩

def decorateErrors (msgs : List String) (p : Parser Γ π α) : Parser Γ π α :=
λ input pos ⇒ match p input pos with
| ParseResult.fail _ _ _ ⇒ ParseResult.fail _ pos msgs
| ok ⇒ ok

def decorateError (msg : String) : Parser Γ π α → Parser Γ π α :=
decorateErrors [ msg ]

def foldrCore (f : α → β → β) (p : Parser Γ π α) (b : β) : Nat → Parser Γ π β
| 0 ⇒ failure
| reps + 1 ⇒
  (do x ← p; xs ← foldrCore reps; pure (f x xs)) <|> pure b

def foldr (f : α → β → β) (p : Parser Γ π α) (b : β) : Parser Γ π β :=
λ input pos ⇒ foldrCore f p b (BuiltFrom.size π input - pos + 1) input pos

def eps : Parser Γ π Unit := pure ()

def many (p : Parser Γ π α) : Parser Γ π (List α) :=
foldr List.cons p []

def many1 (p : Parser Γ π α) : Parser Γ π (List α) :=
List.cons <$> p <*> many p

def fixCore (F : Parser Γ π α → Parser Γ π α) : Nat → Parser Γ π α
| 0 ⇒ failure
| maxDepth + 1 ⇒ F (fixCore maxDepth)

def fix (F : Parser Γ π α → Parser Γ π α) : Parser Γ π α :=
λ input pos ⇒ fixCore F (BuiltFrom.size π input - pos + 1) input pos

def sat (p : π → Bool) : Parser Γ π π :=
λ input pos ⇒
  if pos < BuiltFrom.size π input then
    let c : π := BuiltFrom.get input pos;
    if p c then ParseResult.done (pos + 1) c
    else ParseResult.fail _ pos []
  else ParseResult.fail _ pos []

def byte : Parser Γ π π := sat (λ _ ⇒ true)

def count (p : Parser Γ π α) : ∀ n, Parser Γ π (Vector α n)
| 0 ⇒ pure Vector.nil
| n + 1 ⇒ Vector.cons <$> p <*> count n

def tok (b : π) : Parser Γ π Unit :=
do sat (BuiltFrom.eq Γ b); eps

def remaining : Parser Γ π Nat :=
λ input pos ⇒ ParseResult.done pos (BuiltFrom.size π input - pos)

def eof : Parser Γ π Unit :=
decorateError "<end-of-file>" $
do rem ← remaining; guard (rem = 0)

def run (p : Parser Γ π α) (input : Γ) : Sum String α :=
match (p <* eof) input 0 with
| ParseResult.done pos res ⇒ Sum.inr res
| ParseResult.fail _ pos msg ⇒
  Sum.inl ("expected: " ++ String.intercalate "or " msg)

end Parser
