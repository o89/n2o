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

inductive Integer
| pos : Nat → Integer
| zero
| neg : Nat → Integer

instance Integer.HasToString : HasToString Integer :=
⟨λ x ⇒ match x with
  | Integer.pos x ⇒ toString (x + 1)
  | Integer.zero ⇒ "0"
  | Integer.neg x ⇒ "-" ++ toString (x + 1) ⟩

namespace data.bert

inductive Term
| int : Int → Term
-- | float : Float → Term
| atom : String → Term
| tuple : List Term → Term
| bytelist : ByteString → Term
| list : List Term → Term
| binary : ByteString → Term
| bigint : Integer → Term
| bigbigint : Integer → Term
| nil : Term
| bool : Bool → Term
| dictionary : List (Term × Term) → Term
-- | time : UTCTime → Term
| regex : String → List String → Term

def ct (b : String) (rest : List Term) : Term :=
Term.tuple $ [ Term.atom "bert", Term.atom b ] ++ rest

def compose : Term → Option Term
| Term.nil := Term.list []
| (Term.bool true) := ct "true" []
| (Term.bool false) := ct "false" []
| (Term.dictionary kvs) :=
  ct "dict" [ Term.list $ (λ t ⇒ Term.tuple [Prod.fst t, Prod.snd t]) <$> kvs ]
| (Term.regex s os) :=
  ct "regex" [ Term.bytelist s,
               Term.tuple [ Term.list (Term.atom <$> os) ] ]
| _ := none

partial def Term.toString : Term → String
| (Term.int x) := toString x
| (Term.atom $ String.mk []) := ""
| (Term.atom s@(String.mk $ x :: xs)) :=
  if x.isLower then s
  else "'" ++ s ++ "'"
| (Term.tuple ts) := "{" ++ String.intercalate ", " (Term.toString <$> ts) ++ "}"
| (Term.bytelist s) := "[" ++ toString s ++ "]"
| (Term.list ts) := "[" ++ String.intercalate ", " (Term.toString <$> ts) ++ "]"
| (Term.binary s) :=
  let wrap := λ s ⇒ "<<" ++ s ++ ">>";
  if s.all Char.isAscii then wrap ("\"" ++ s ++ "\"")
  else wrap (toString s)
| (Term.bigint x) := toString x
| (Term.bigbigint x) := toString x
| t := Option.getOrElse (Term.toString <$> compose t) ""
instance : HasToString Term := ⟨Term.toString⟩

class BERT (α : Type) :=
(toTerm {} : α → Term)
(fromTerm {} : Term → Sum String α)

instance Term.BERT : BERT Term :=
{ toTerm := id, fromTerm := Sum.inr }

instance Int.BERT : BERT Int :=
{ toTerm := Term.int,
  fromTerm := λ t ⇒ match t with
    | Term.int val ⇒ Sum.inr val
    | _ ⇒ Sum.inl "invalid integer type" }

instance Bool.BERT : BERT Bool :=
{ toTerm := Term.bool,
  fromTerm := λ t ⇒ match t with
    | Term.bool x ⇒ Sum.inr x
    | _ ⇒ Sum.inl "invalid bool type" }

instance Integer.BERT : BERT Integer :=
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
    --| Term.list xs
    | _ ⇒ Sum.inl "invalid string type" }

instance ByteString.BERT : BERT ByteString :=
{ toTerm := Term.bytelist,
  fromTerm := λ t ⇒ match t with
    | Term.bytelist x ⇒ Sum.inr x
    | _ ⇒ Sum.inl "invalid bytestring type" }

def Sum.HasMap {γ α β : Type} : (α → β) → Sum γ α → Sum γ β
| f (Sum.inr val) := Sum.inr (f val)
| _ (Sum.inl er)  := Sum.inl er

instance {α : Type} : Functor (Sum α) :=
{ map := @Sum.HasMap α }

def Sum.HasSeq {γ α β : Type} : Sum γ (α → β) → Sum γ α → Sum γ β
| (Sum.inr f) (Sum.inr x) := Sum.inr (f x)
| (Sum.inl er) _ := Sum.inl er
| _ (Sum.inl er) := Sum.inl er

instance {α : Type} : Applicative (Sum α) :=
{ pure := λ _ x ⇒ Sum.inr x,
  seq := @Sum.HasSeq α }

def Sum.HasBind {α β γ : Type} : Sum α β → (β → Sum α γ) → Sum α γ
| (Sum.inr val) f := f val
| (Sum.inl er)  _ := Sum.inl er

instance {α : Type} : Monad (Sum α) :=
{ pure := λ _ x ⇒ Sum.inr x,
  bind := @Sum.HasBind α }

def mapM {m : Type → Type} [Monad m] {α β : Type} (f : α → m β) : List α → m (List β)
| [] := pure []
| (x :: xs) := do
  ys ← mapM xs;
  y ← f x;
  pure (y :: ys)

instance List.BERT {α : Type} [BERT α] : BERT (List α) :=
{ toTerm := λ xs ⇒ Term.list (BERT.toTerm <$> xs),
  fromTerm := λ t ⇒ match t with
    | Term.list xs ⇒ mapM BERT.fromTerm xs
    | _ ⇒ Sum.inl "invalid list type" }

instance Tuple.BERT {α β : Type} [BERT α] [BERT β] : BERT (α × β) :=
{ toTerm := λ x ⇒ Term.tuple [ BERT.toTerm (Prod.fst x), BERT.toTerm (Prod.snd x) ],
  fromTerm := λ t ⇒ match t with
    | Term.tuple [a, b] ⇒ do
      x ← BERT.fromTerm a;
      y ← BERT.fromTerm b;
      pure (x, y)
    | _ ⇒ Sum.inl "invalid tuple type" }

-- TODO: BERT of Map

end data.bert
