-- data.buffer.parser from Lean 3 stdlib

inductive ParseResult (α : Type)
| done (pos : Nat) (result : α) : ParseResult
| fail (pos : Nat) (msg : List String) : ParseResult

def ByteParser (α : Type) :=
∀ (input : ByteArray) (start : Nat), ParseResult α

namespace ByteParser
variables {α β : Type}

protected def bind (p : ByteParser α) (f : α → ByteParser β) : ByteParser β :=
λ input pos ⇒ match p input pos with
| ParseResult.done pos a ⇒ f a input pos
| ParseResult.fail _ pos msg ⇒ ParseResult.fail β pos msg

protected def pure (a : α) : ByteParser α :=
λ input pos ⇒ ParseResult.done pos a

protected def fail (msg : String) : ByteParser α :=
λ _ pos ⇒ ParseResult.fail α pos [ msg ]

instance : Monad ByteParser :=
{ pure := @ByteParser.pure, bind := @ByteParser.bind }

instance : MonadFail ByteParser :=
{ fail := @ByteParser.fail }

protected def failure : ByteParser α :=
λ _ pos ⇒ ParseResult.fail α pos []

protected def orelse (p q : ByteParser α) : ByteParser α :=
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

instance : Alternative ByteParser :=
{ failure := @ByteParser.failure, orelse := @ByteParser.orelse }

instance : Inhabited (ByteParser α) := ⟨failure⟩

def decorateErrors (msgs : List String) (p : ByteParser α) : ByteParser α :=
λ input pos ⇒ match p input pos with
| ParseResult.fail _ _ _ ⇒ ParseResult.fail _ pos msgs
| ok ⇒ ok

def decorateError (msg : String) : ByteParser α → ByteParser α :=
decorateErrors [ msg ]

def eps : ByteParser Unit := pure ()

def sat (p : UInt8 → Bool) : ByteParser UInt8 :=
λ input pos ⇒
  if pos < input.size then
    let c := input.get pos;
    if p c then ParseResult.done (pos + 1) c
    else ParseResult.fail _ pos []
  else ParseResult.fail _ pos []

def byte : ByteParser UInt8 := sat (λ _ ⇒ true)

def tok (b : UInt8) : ByteParser Unit :=
decorateError (toString b) (do sat (HasBeq.beq b); eps)

def remaining : ByteParser Nat :=
λ input pos ⇒ ParseResult.done pos (input.size - pos)

def eof : ByteParser Unit :=
decorateError "<end-of-file>" $
do rem ← remaining; guard (rem = 0)

def run (p : ByteParser α) (input : ByteArray) : Sum String α :=
match (p <* eof) input 0 with
| ParseResult.done pos res ⇒ Sum.inr res
| ParseResult.fail _ pos msg ⇒
  Sum.inl ("expected: " ++ String.intercalate "or " msg)

end ByteParser
