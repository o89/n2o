-- data.buffer.parser from Lean 3 stdlib
import N2O.Data.Bytes
import N2O.Data.Vector

inductive ParseResult (α : Type)
| done (pos : Nat) (result : α) : ParseResult
| fail (pos : Nat) (msg : List String) : ParseResult

class BuiltFrom (Γ : Type) (π : Type) :=
(size {} : Γ → Nat)
(eq {} : π → π → Bool)
(get {} : Γ → Nat → π)
(escape {} : π → String)

def Parser (Γ π : Type) [BuiltFrom Γ π] (α : Type) :=
∀ (input : Γ) (start : Nat), ParseResult α

instance : BuiltFrom ByteArray UInt8 :=
{ size := ByteArray.size,
  eq := HasBeq.beq,
  get := ByteArray.get!,
  escape := toString }

abbrev ByteParser := Parser ByteArray UInt8

def ByteParser.ch : ByteParser Char :=
λ input pos ⇒
  if pos < input.size then
    let ch := UInt32.ofNat (input.get! pos).toNat;
    if h : isValidChar ch then ParseResult.done (pos + 1) (Char.mk ch h)
    else ParseResult.fail _ pos [ "<valid char>" ]
  else ParseResult.fail _ pos [ "<char>" ]

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

partial def countLength (p : Parser Γ π (α × Nat)) : Nat → Parser Γ π (List α)
| 0 ⇒ pure []
| m ⇒ do (x, n) ← p; xs ← countLength (m - n); pure (x :: xs)

def tok (b : π) : Parser Γ π Unit :=
decorateError (BuiltFrom.escape Γ b) $ do sat (BuiltFrom.eq Γ b); eps

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

def Prod.rev {α β : Type} (y : β) (x : α) : α × β := (x, y)

namespace ByteParser.utf8
  def isHelpful (x : UInt8) : Bool := x.shiftr 6 = 0b10

  def isFirst (x : UInt8) : Bool := x.shiftr 7 = 0
  def isSecond (x : UInt8) : Bool := x.shiftr 5 = 0b110
  def isThird (x : UInt8) : Bool := x.shiftr 4 = 0b1110
  def isFourth (x : UInt8) : Bool := x.shiftr 3 = 0b11110

  def parseValidChar (x : UInt32) : ByteParser Char :=
    if h : isValidChar x then pure (Char.mk x h)
    else Parser.fail "invalid character"

  def readFirst : ByteParser (Char × Nat) := Parser.decorateError "<1>" $ do
    a ← Parser.byte; guard (isFirst a); Prod.rev 1 <$> parseValidChar a.toUInt32

  def readSecond : ByteParser (Char × Nat) := Parser.decorateError "<2>" $ do
    a ← Parser.byte; b ← Parser.byte;
    guard (isSecond a); guard (isHelpful b);
    Prod.rev 2 <$> (parseValidChar $
      (a.toUInt32.land 0b00011111).shiftl 6 +
       b.toUInt32.land 0b00111111)

  def readThird : ByteParser (Char × Nat) := Parser.decorateError "<3>" $ do
    a ← Parser.byte; b ← Parser.byte; c ← Parser.byte;
    guard (isThird a); guard (isHelpful b); guard (isHelpful c);
    Prod.rev 3 <$> (parseValidChar $
      (a.toUInt32.land 0b00001111).shiftl 12 +
      (b.toUInt32.land 0b00111111).shiftl 6 +
       c.toUInt32.land 0b00111111 )

  def readFourth : ByteParser (Char × Nat) := Parser.decorateError "<4>" $ do
    a ← Parser.byte; b ← Parser.byte; c ← Parser.byte; d ← Parser.byte;
    guard (isFourth a); guard (isHelpful b);
    guard (isHelpful c); guard (isHelpful d);
    Prod.rev 4 <$> (parseValidChar $
      (a.toUInt32.land 0b00000111).shiftl 18 +
      (b.toUInt32.land 0b00111111).shiftl 12 +
      (c.toUInt32.land 0b00111111).shiftl 6 +
       d.toUInt32.land 0b00111111)

  def uchr := readFirst <|> readSecond <|> readThird <|> readFourth
  def stringWithLength (s : Nat) : ByteParser String :=
  String.mk <$> Parser.countLength uchr s
end ByteParser.utf8

