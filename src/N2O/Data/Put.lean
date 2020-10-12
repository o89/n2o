import N2O.Data.Bytes
import N2O.Data.Sum

def PutM (α : Type) := α × ByteArray

namespace PutM
  def HasMap {α β : Type} (f : α → β) : PutM α → PutM β
  | (a, w) => (f a, w)

  instance : Functor PutM := 
  { map := @HasMap }

  def pure {α : Type} (x : α) : PutM α := (x, ByteArray.empty)

  instance : HasPure PutM :=
  { pure := @pure }

  def HasSeq {α β : Type} : PutM (α → β) → PutM α → PutM β
  | (f, w), (x, w') => (f x, w ++ w')

  instance : Applicative PutM :=
  { pure := @pure, seq := @HasSeq }

  def bind {α β : Type} : PutM α → (α → PutM β) → PutM β
  | (a, w), f => match f a with
  | (b, w') => (b, w ++ w')

  instance : HasBind PutM :=
  { bind := @bind }
end PutM

inductive Put.Result
| ok | error : String → Put.Result

abbrev Put := PutM Put.Result

def Put.tell (x : ByteArray) : Put := (Put.Result.ok, x)

def Put.raw (x : UInt8) : Put := Put.tell [x].toByteArray

def Put.byte (x : Nat) : Put := Put.raw (UInt8.ofNat x)
def Put.word (x : Nat) : Put := Put.tell (UInt16.ofNat x).toBytes
def Put.dword (x : Nat) : Put := Put.tell (UInt32.ofNat x).toBytes

def Put.run : Put → Sum String ByteArray
| (Put.Result.ok, arr) => Sum.ok arr
| (Put.Result.error s, _) => Sum.fail s

def Put.fail : String → PutM Put.Result := pure ∘ Put.Result.error
def Put.nope : PutM Put.Result := pure Put.Result.ok

instance : HasAndthen (PutM Put.Result) := ⟨λ x y => do x >>= λ _ => y⟩
instance : Inhabited Put := ⟨Put.fail "unreacheable code was reached"⟩

def Put.uchr (ch : Char) : Put :=
let x := UInt32.ofNat ch.val.toNat;
if x < 0x80 then Put.raw x.toUInt8
else if x < 0x800 then
  Put.raw ((x.land 0b11111000000).shiftr 6 + 0b11000000).toUInt8 >>
  Put.raw (x.land 0b111111 + 0b10000000).toUInt8
else if x < 0x10000 then
  Put.raw ((x.land 0b1111000000000000).shiftr 12 + 0b11100000).toUInt8 >>
  Put.raw ((x.land 0b111111000000).shiftr 6 + 0b10000000).toUInt8 >>
  Put.raw (x.land 0b111111 + 0b10000000).toUInt8
else if x < 0x110000 then
  Put.raw ((x.land 0b111000000000000000000).shiftr 18 + 0b11110000).toUInt8 >>
  Put.raw ((x.land 0b111111000000000000).shiftr 12 + 0b10000000).toUInt8 >>
  Put.raw ((x.land 0b111111000000).shiftr 6 + 0b10000000).toUInt8 >>
  Put.raw (x.land 0b111111 + 0b10000000).toUInt8
else Put.fail "character too big"

def Put.unicode (s : String) : Put :=
List.foldr (HasAndthen.andthen ∘ Put.uchr) Put.nope s.toList
