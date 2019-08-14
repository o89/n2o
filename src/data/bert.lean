import data.parser

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
end Sum

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
| binary : ByteString → Term
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
| Term.binary s ⇒
  let wrap := λ s ⇒ "<<" ++ s ++ ">>";
  if s.all Char.isAscii then wrap ("\"" ++ s ++ "\"")
  else wrap (toString s)
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
    | Term.binary x ⇒ Sum.inr x
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

def iota : Nat → List Nat
| 0     ⇒ [ 0 ]
| n + 1 ⇒ (n + 1) :: iota n

@[extern cpp inline "#1 << #2"]
constant UInt16.shiftl (a b : UInt16) : UInt16 := UInt16.ofNat (default _)
@[extern cpp inline "#1 >> #2"]
constant UInt16.shiftr (a b : UInt16) : UInt16 := UInt16.ofNat (default _)

@[extern cpp inline "#1 << #2"]
constant UInt32.shiftl (a b : UInt32) : UInt32 := UInt32.ofNat (default _)
@[extern cpp inline "#1 >> #2"]
constant UInt32.shiftr (a b : UInt32) : UInt32 := UInt32.ofNat (default _)

def UInt32.nthByte (x : UInt32) (n : Nat) : UInt8 :=
UInt8.ofNat (UInt32.land (UInt32.shiftr x $ 8 * UInt32.ofNat n) 255).toNat

def UInt32.toBytes (x : UInt32) : ByteArray :=
List.toByteArray $ UInt32.nthByte x <$> iota 3

def UInt8.shiftl16 (x : UInt8) (y : UInt16) : UInt16 :=
UInt16.shiftl (UInt16.ofNat x.toNat) y

def UInt8.shiftl32 (x : UInt8) (y : UInt32) : UInt32 :=
UInt32.shiftl (UInt32.ofNat x.toNat) y

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

def readDword : ByteParser Term := do
  Parser.tok 98; res ← dword;
  pure (Term.int res)

end data.bert
