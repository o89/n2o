import N2O.Data.Bytes
import N2O.Data.Sum

def PutM (α : Type) := α × ByteArray

namespace PutM
  def HasMap {α β : Type} (f : α → β) : PutM α → PutM β
  | (a, w) => (f a, w)

  instance : Functor PutM := 
  { map := HasMap }

  def pure {α : Type} (x : α) : PutM α := (x, ByteArray.empty)

  def HasSeq {α β : Type} (a : PutM (α → β)) (b : Unit → PutM α) : PutM β :=
  match a, b () with | (f, w), (x, w') => (f x, w ++ w')

  instance : Applicative PutM :=
  { pure := pure, seq := HasSeq }

  def bind {α β : Type} : PutM α → (α → PutM β) → PutM β
  | (a, w), f => match f a with
  | (b, w') => (b, w ++ w')

  instance : Monad PutM :=
  { bind := bind }
end PutM

inductive Report
| ok | error : String → Report

abbrev Put := PutM Report

def Put.tell (x : ByteArray) : Put := (Report.ok, x)

def Put.raw (x : UInt8) : Put := Put.tell [x].toByteArray

def Put.byte  (x : Nat) : Put := Put.raw (UInt8.ofNat x)
def Put.word  (x : Nat) : Put := Put.tell (UInt16.ofNat x).toBytes
def Put.dword (x : Nat) : Put := Put.tell (UInt32.ofNat x).toBytes

def Put.run : Put → Sum String ByteArray
| (Report.ok, arr) => Sum.ok arr
| (Report.error s, _) => Sum.fail s

def Put.fail : String → PutM Report := pure ∘ Report.error
def Put.nope : PutM Report := pure Report.ok

instance : HAndThen Put Put Put := ⟨λ x y => do x >>= λ _ => y ()⟩
instance : Inhabited Put        := ⟨Put.fail "unreacheable code was reached"⟩

def Put.uchr (ch : Char) : Put :=
let x := UInt32.ofNat ch.val.toNat;
let out := Put.raw ∘ UInt32.toUInt8;
if x < 0x80 then Put.raw x.toUInt8
else if x < 0x800 then
  out ((x.land 0b11111000000).shiftRight 6 + 0b11000000) >>
  out (x.land 0b111111 + 0b10000000)
else if x < 0x10000 then
  out ((x.land 0b1111000000000000).shiftRight 12 + 0b11100000) >>
  out ((x.land 0b111111000000).shiftRight 6 + 0b10000000) >>
  out (x.land 0b111111 + 0b10000000)
else if x < 0x110000 then
  out ((x.land 0b111000000000000000000).shiftRight 18 + 0b11110000) >>
  out ((x.land 0b111111000000000000).shiftRight 12 + 0b10000000) >>
  out ((x.land 0b111111000000).shiftRight 6 + 0b10000000) >>
  out (x.land 0b111111 + 0b10000000)
else Put.fail "character too big"

def Put.unicode (s : String) : Put :=
List.foldr (λ ch fn => Put.uchr ch >> fn) Put.nope s.toList
