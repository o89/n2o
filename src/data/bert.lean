import data.parser

@[extern cpp inline "#1 << #2"]
constant UInt16.shiftl (a b : UInt16) : UInt16 := UInt16.ofNat (default _)
@[extern cpp inline "#1 >> #2"]
constant UInt16.shiftr (a b : UInt16) : UInt16 := UInt16.ofNat (default _)

@[extern cpp inline "#1 << #2"]
constant UInt32.shiftl (a b : UInt32) : UInt32 := UInt32.ofNat (default _)
@[extern cpp inline "#1 >> #2"]
constant UInt32.shiftr (a b : UInt32) : UInt32 := UInt32.ofNat (default _)

def UInt16.crop (x : UInt16) : UInt8 := UInt8.ofNat x.toNat
def UInt32.crop (x : UInt32) : UInt8 := UInt8.ofNat x.toNat

def UInt16.nthByte (x : UInt16) (n : Nat) : UInt8 :=
(UInt16.land (UInt16.shiftr x $ 8 * UInt16.ofNat n) 255).crop

def UInt32.nthByte (x : UInt32) (n : Nat) : UInt8 :=
(UInt32.land (UInt32.shiftr x $ 8 * UInt32.ofNat n) 255).crop

def List.iotaZero : Nat → List Nat
| 0     ⇒ [ 0 ]
| n + 1 ⇒ (n + 1) :: List.iotaZero n

def UInt16.toBytes (x : UInt16) : List UInt8 :=
UInt16.nthByte x <$> List.iotaZero 3

def UInt32.toBytes (x : UInt32) : List UInt8 :=
UInt32.nthByte x <$> List.iotaZero 3

def UInt8.shiftl16 (x : UInt8) (y : UInt16) : UInt16 :=
UInt16.shiftl (UInt16.ofNat x.toNat) y

def UInt8.shiftl32 (x : UInt8) (y : UInt32) : UInt32 :=
UInt32.shiftl (UInt32.ofNat x.toNat) y

def String.bytes (x : String) : List UInt8 :=
(UInt8.ofNat ∘ Char.toNat) <$> x.toList

inductive DayOfWeek
| monday   | tuesday | wednesday
| thursday | friday
| saturday | sunday

def DayOfWeek.toNat (dow : DayOfWeek) : UInt32 :=
DayOfWeek.casesOn dow 1 2 3 4 5 6 7

inductive Month
| jan | feb | mar
| apr | may | jun
| jul | aug | sep
| oct | nov | dec

def Month.toNat (m : Month) : Nat :=
Month.casesOn m 1 2 3 4 5 6 7 8 9 10 11 12

instance Month.HasToString : HasToString Month :=
⟨λ m ⇒ Month.casesOn m
  "January" "February" "March"
  "April" "May" "June"
  "July" "August" "September"
  "October" "November" "December"⟩

instance Month.HasRepr : HasRepr Month :=
⟨λ m ⇒ Month.casesOn m
  "jan" "feb" "mar"
  "apr" "may" "jun"
  "jul" "aug" "sep"
  "oct" "nov" "dec"⟩

-- TODO: UTCTime
structure Date :=
(year : Nat)
(month : Month)
(day : Nat)
(hour : Nat)
(minute : Nat)
(seconds : Nat)
(nanoseconds : Nat)

def Char.isAscii (c : Char) : Bool :=
c.val ≤ 127

def ByteString := String
instance ByteString.HasToString : HasToString ByteString :=
⟨λ s ⇒ String.intercalate ", " $ (toString ∘ Char.toNat) <$> s.toList⟩

def mapM {m : Type → Type} [Monad m] {α β : Type} (f : α → m β) : List α → m (List β)
| [] ⇒ pure []
| x :: xs ⇒ do
  ys ← mapM xs;
  y ← f x;
  pure (y :: ys)

namespace Sum
  def HasMap {γ α β : Type} : (α → β) → Sum γ α → Sum γ β
  | f, Sum.inr val ⇒ Sum.inr (f val)
  | _, Sum.inl er  ⇒ Sum.inl er

  instance {α : Type} : Functor (Sum α) :=
  { map := @HasMap α }

  def HasSeq {γ α β : Type} : Sum γ (α → β) → Sum γ α → Sum γ β
  | Sum.inr f, Sum.inr x ⇒ Sum.inr (f x)
  | Sum.inl er, _ ⇒ Sum.inl er
  | _, Sum.inl er ⇒ Sum.inl er

  instance {α : Type} : Applicative (Sum α) :=
  { pure := λ _ x ⇒ Sum.inr x,
    seq := @HasSeq α }

  def HasBind {α β γ : Type} : Sum α β → (β → Sum α γ) → Sum α γ
  | Sum.inr val, f ⇒ f val
  | Sum.inl er,  _ ⇒ Sum.inl er

  instance {α : Type} : Monad (Sum α) :=
  { pure := λ _ x ⇒ Sum.inr x,
    bind := @HasBind α }

  @[matchPattern] abbrev fail {α β : Type} : α → Sum α β := Sum.inl
  @[matchPattern] abbrev ok {α β : Type} : β → Sum α β := Sum.inr
end Sum

def Put := ByteArray → Sum String ByteArray

namespace Put
   def byte (x : UInt8) : Put :=
   λ arr ⇒ Sum.ok (ByteArray.push arr x)

   def tell : List UInt8 → Put :=
   List.foldr (mcomp ∘ byte) pure

   def run (p : Put) : Sum String ByteArray := p ByteArray.empty

   def fail (s : String) : Put := λ _ ⇒ Sum.fail s
end Put

namespace data.bert

inductive Term
| byte : UInt8 → Term
-- there is now no Int32 in Lean
| int : UInt32 → Term
-- | float : Float → Term
| atom : String → Term
| tuple : List Term → Term
| bytelist : ByteString → Term
| list : List Term → Term
| binary : ByteArray → Term
| bigint : Int → Term
| bigbigint : Int → Term

inductive CompTerm
| nil : CompTerm
| bool : Bool → CompTerm
| dictionary : List (Term × Term) → CompTerm
-- | time : UTCTime → CompTerm
| regex : String → List String → CompTerm

def ct (b : String) (rest : List Term) : Term :=
Term.tuple $ [ Term.atom "bert", Term.atom b ] ++ rest

@[matchPattern] def compose : CompTerm → Term
| CompTerm.nil ⇒ Term.list []
| CompTerm.bool true ⇒ ct "true" []
| CompTerm.bool false ⇒ ct "false" []
| CompTerm.dictionary kvs ⇒
  ct "dict" [ Term.list $ (λ t ⇒ Term.tuple [Prod.fst t, Prod.snd t]) <$> kvs ]
| CompTerm.regex s os ⇒
  ct "regex" [ Term.bytelist s,
               Term.tuple [ Term.list (Term.atom <$> os) ] ]

partial def Term.toString : Term → String
| Term.byte x ⇒ toString x
| Term.int x ⇒ toString x
| Term.atom (String.mk []) ⇒ ""
| Term.atom s@(String.mk $ x :: xs) ⇒
  if x.isLower then s
  else "'" ++ s ++ "'"
| Term.tuple ts ⇒ "{" ++ String.intercalate ", " (Term.toString <$> ts) ++ "}"
| Term.bytelist s ⇒ "[" ++ toString s ++ "]"
| Term.list ts ⇒ "[" ++ String.intercalate ", " (Term.toString <$> ts) ++ "]"
| Term.binary s ⇒ "<<" ++ String.intercalate ", " (toString <$> s.toList) ++ ">>"
| Term.bigint x ⇒ toString x
| Term.bigbigint x ⇒ toString x
instance : HasToString Term := ⟨Term.toString⟩

class BERT (α : Type) :=
(toTerm {} : α → Term)
(fromTerm {} : Term → Sum String α)

instance Term.BERT : BERT Term :=
{ toTerm := id, fromTerm := Sum.inr }

instance Int.BERT : BERT UInt32 :=
{ toTerm := Term.int,
  fromTerm := λ t ⇒ match t with
    | Term.int val ⇒ Sum.inr val
    | _ ⇒ Sum.inl "invalid integer type" }

instance Bool.BERT : BERT Bool :=
{ toTerm := compose ∘ CompTerm.bool,
  fromTerm := λ t ⇒ match t with
    | compose (CompTerm.bool true) ⇒ Sum.inr true
    | compose (CompTerm.bool false) ⇒ Sum.inr false
    | _ ⇒ Sum.inl "invalid bool type" }

instance Integer.BERT : BERT Int :=
{ toTerm := Term.bigbigint,
  fromTerm := λ t ⇒ match t with
    | Term.bigint x ⇒ Sum.inr x
    | Term.bigbigint x ⇒ Sum.inr x
    | _ ⇒ Sum.inl "invalid integer type" }

instance String.BERT : BERT String :=
{ toTerm := Term.bytelist,
  fromTerm := λ t ⇒ match t with
    | Term.bytelist x ⇒ Sum.inr x
    | Term.atom x ⇒ Sum.inr x
    | _ ⇒ Sum.inl "invalid string type" }

instance ByteString.BERT : BERT ByteString :=
{ toTerm := Term.bytelist,
  fromTerm := λ t ⇒ match t with
    | Term.bytelist x ⇒ Sum.inr x
    | _ ⇒ Sum.inl "invalid bytestring type" }

instance List.BERT {α : Type} [BERT α] : BERT (List α) :=
{ toTerm := λ xs ⇒ Term.list (BERT.toTerm <$> xs),
  fromTerm := λ t ⇒ match t with
    | Term.list xs ⇒ mapM BERT.fromTerm xs
    | _ ⇒ Sum.inl "invalid list type" }

instance Tuple.BERT {α β : Type} [BERT α] [BERT β] : BERT (α × β) :=
{ toTerm := λ x ⇒ Term.tuple [ BERT.toTerm x.1, BERT.toTerm x.2 ],
  fromTerm := λ t ⇒ match t with
    | Term.tuple [a, b] ⇒ do
      x ← BERT.fromTerm a;
      y ← BERT.fromTerm b;
      pure (x, y)
    | _ ⇒ Sum.inl "invalid tuple type" }

def word : ByteParser UInt16 := do
  res ← Parser.count Parser.byte 2;
  match res with
  | a ∷ b ∷ Vector.nil ⇒
    let a' := UInt8.shiftl16 a (8 * 1);
    let b' := UInt8.shiftl16 b (8 * 0);
    pure (a' + b')

def dword : ByteParser UInt32 := do
  res ← Parser.count Parser.byte 4;
  match res with
  | a ∷ b ∷ c ∷ d ∷ Vector.nil ⇒
    let a' := UInt8.shiftl32 a (8 * 3);
    let b' := UInt8.shiftl32 b (8 * 2);
    let c' := UInt8.shiftl32 c (8 * 1);
    let d' := UInt8.shiftl32 d (8 * 0);
    pure (a' + b' + c' + d')

def readByte : ByteParser Term := do
  Parser.tok 97; val ← Parser.byte;
  pure (Term.byte val)

def writeByte (x : UInt8) : Put :=
  Put.byte 97 >=> Put.byte x

def readDword : ByteParser Term := do
  Parser.tok 98; res ← dword;
  pure (Term.int res)

def writeDword (x : UInt32) : Put :=
  Put.byte 98 >=> Put.tell x.toBytes

def ch : ByteParser Char :=
λ input pos ⇒
  if pos < input.size then
    let ch := UInt32.ofNat (input.get pos).toNat;
    if h : isValidChar ch then ParseResult.done (pos + 1) (Char.mk ch h)
    else ParseResult.fail _ pos [ "<valid char>" ]
  else ParseResult.fail _ pos [ "<char>" ]

def readAtom : ByteParser Term := do
  Parser.tok 100; N ← word;
  chars ← Parser.count ch N.toNat;
  pure (Term.atom chars.toList.asString)

def readSmallAtom : ByteParser Term := do
  Parser.tok 115; N ← Parser.byte;
  chars ← Parser.count ch N.toNat;
  pure (Term.atom chars.toList.asString)

def writeAtom (x : String) : Put :=
  if x.length < uint8Sz then
    Put.byte 115 >=> Put.byte (UInt8.ofNat x.length) >=> Put.tell x.bytes
  else if x.length < uint16Sz then
    Put.byte 100 >=> Put.tell (UInt16.ofNat x.length).toBytes >=> Put.tell x.bytes
  else Put.fail "BERT atom too long (≥ 65536)"

def readTuple (readTerm : ByteParser Term) : ByteParser Term := do
  Parser.tok 104; N ← Parser.byte;
  elems ← Parser.count readTerm N.toNat;
  pure (Term.tuple elems.toList)

def readLargeTuple (readTerm : ByteParser Term) : ByteParser Term := do
  Parser.tok 105; N ← dword;
  elems ← Parser.count readTerm N.toNat;
  pure (Term.tuple elems.toList)

def readNil : ByteParser Term := do Parser.tok 106; pure (Term.list [])
def readList (readTerm : ByteParser Term) : ByteParser Term := do
  Parser.tok 108; N ← dword;
  elems ← Parser.count readTerm N.toNat;
  optional readNil;
  pure (Term.list elems.toList)

def readBinary : ByteParser Term := do
  Parser.tok 109; N ← dword;
  elems ← Parser.count Parser.byte N.toNat;
  pure (Term.binary elems.toList.toByteArray)

def IsMinus : ByteParser Bool :=
(do Parser.tok 0; pure false) <|>
(do Parser.tok 1; pure true)

def readBignum' {α : Type}
  (p : ByteParser α) (toNat : α → Nat) (tok : UInt8) :
  ByteParser Term := do
  Parser.tok 110; n ← p;
  isMinus ← IsMinus; d ← Parser.count Parser.byte (toNat n);
  let x := Int.ofNat
    (List.foldl Nat.add 0 $
      (λ (pair : Nat × UInt8) ⇒
        pair.2.toNat * (256 ^ pair.1)) <$> d.toList.enum);
  pure (Term.bigint $ if isMinus then -x else x)

def readSmallBignum := readBignum' Parser.byte UInt8.toNat 110
def readLargeBignum := readBignum' dword UInt32.toNat 111

def readTerm' (readTerm : ByteParser Term) : ByteParser Term :=
readByte <|> readDword <|> readAtom <|>
readTuple readTerm <|> readLargeTuple readTerm <|>
readList readTerm <|> readBinary <|> readSmallAtom <|>
readSmallBignum <|> readLargeBignum

def readTerm := do Parser.tok 131; Parser.fix readTerm'

end data.bert
