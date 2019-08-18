import data.bytes data.sum

def PutM (α : Type) := α × ByteArray

namespace PutM
  def HasMap {α β : Type} (f : α → β) : PutM α → PutM β
  | (a, w) ⇒ (f a, w)

  instance : Functor PutM := 
  { map := @HasMap }

  def pure {α : Type} (x : α) : PutM α := (x, ByteArray.empty)

  def HasSeq {α β : Type} : PutM (α → β) → PutM α → PutM β
  | (f, w), (x, w') ⇒ (f x, w ++ w')

  instance : Applicative PutM :=
  { pure := @pure, seq := @HasSeq }

  def bind {α β : Type} : PutM α → (α → PutM β) → PutM β
  | (a, w), f ⇒ match f a with
  | (b, w') ⇒ (b, w ++ w')

  instance : Monad PutM :=
  { bind := @bind }
end PutM

inductive Put.Result
| ok | error : String → Put.Result

abbrev Put := PutM Put.Result
def Put.tell (x : ByteArray) : Put := (Put.Result.ok, x)

def Put.raw (x : UInt8) : Put := Put.tell [ x ].toByteArray

def Put.byte (x : Nat) : Put := Put.raw (UInt8.ofNat x)
def Put.word (x : Nat) : Put := Put.tell (UInt16.ofNat x).toBytes
def Put.dword (x : Nat) : Put := Put.tell (UInt32.ofNat x).toBytes

def Put.run : Put → Sum String ByteArray
| (Put.Result.ok, arr) ⇒ Sum.ok arr
| (Put.Result.error s, _) ⇒ Sum.fail s

def Put.fail : String → Put := pure ∘ Put.Result.error
def Put.nope : Put := pure Put.Result.ok

instance : HasAndthen Put := ⟨λ x y ⇒ do x; y⟩
instance : Inhabited Put := ⟨Put.fail "unreacheable code was reached"⟩
