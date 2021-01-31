import N2O.Data.Bytes
import N2O.Data.Sum
import N2O.Data.Put
import N2O.Data.Parser

def Char.isAscii (c : Char) : Bool :=
c.val ≤ 127

def mapM {m : Type → Type} [Monad m] {α β : Type} (f : α → m β) : List α → m (List β)
| [] => pure []
| x :: xs => do
  let ys ← mapM f xs;
  let y ← f x;
  pure (y :: ys)

abbrev Dict (α β : Type) := List (α × β)

inductive Term
| byte   : UInt8 → Term
-- there is now no Int32 in Lean
| int    : UInt32 → Term
--| float  : Float → Term
| atom   : String → Term
| tuple  : List Term → Term
| string : String → Term
| list   : List Term → Term
| binary : ByteArray → Term
| bigint : Int → Term
| dict   : List (Term × Term) → Term

partial def showTerm : Term → String
| Term.byte x => toString x
| Term.int x => toString x
| Term.atom (String.mk []) => ""
| Term.atom s@(String.mk $ x :: xs) =>
  if x.isLower then s
  else "'" ++ s ++ "'"
| Term.tuple ts => "{" ++ String.intercalate ", " (List.map showTerm ts) ++ "}"
| Term.string s => "\"" ++ s ++ "\""
| Term.list ts => "[" ++ String.intercalate ", " (List.map showTerm ts) ++ "]"
| Term.binary s => "<<" ++ String.intercalate ", " (List.map toString s.toList) ++ ">>"
| Term.bigint x => toString x
| Term.dict x =>
  let printPair := λ (pair : Term × Term) =>
    "{" ++ showTerm pair.1 ++ ", " ++ showTerm pair.2 ++ "}";
  "[" ++ String.intercalate ", " (List.map printPair x) ++ "]"
instance : ToString Term := ⟨showTerm⟩

class BERT (α : Type) :=
(toTerm   : α → Term)
(fromTerm : Term → Sum String α)

instance Term.BERT : BERT Term :=
{ toTerm := id, fromTerm := Sum.inr }

instance Int.BERT : BERT UInt32 :=
{ toTerm := Term.int,
  fromTerm := λ t => match t with
    | Term.int val => Sum.inr val
    | _ => Sum.inl "invalid integer type" }

instance Integer.BERT : BERT Int :=
{ toTerm := Term.bigint,
  fromTerm := λ t => match t with
    | Term.bigint x => Sum.inr x
    | _ => Sum.inl "invalid integer type" }

instance String.BERT : BERT String :=
{ toTerm := Term.string,
  fromTerm := λ t => match t with
    | Term.string x => Sum.inr x
    | Term.atom x => Sum.inr x
    | _ => Sum.inl "invalid string type" }

section
  variable {α : Type} [BERT α]

  def listToTerm := Term.list ∘ @List.map α Term BERT.toTerm
  def listFromTerm : Term → Sum String (List α)
  | Term.list xs => mapM BERT.fromTerm xs
  | _ => Sum.inl "given BERT term is not a list"

  instance List.BERT : BERT (List α) := ⟨listToTerm, listFromTerm⟩
end

section
  variable {α β : Type} [BERT α] [BERT β]

  def dictToTerm :=
  Term.dict ∘ @List.map (α × β) (Term × Term) (Prod.map BERT.toTerm BERT.toTerm)

  def termFromPair (p : Term × Term) : Sum String (α × β) := do
    let fst ← BERT.fromTerm p.1;
    let snd ← BERT.fromTerm p.2;
    pure (fst, snd)

  def dictFromTerm : Term → Sum String (Dict α β)
  | Term.dict xs => mapM termFromPair xs
  | _ => Sum.inl "given BERT term is not a dictionary"

  instance Dict.BERT : BERT (Dict α β) := ⟨dictToTerm, dictFromTerm⟩
end

section
  variable {α β : Type} [BERT α] [BERT β]

  def pairToTerm : α × β → Term :=
  λ (a, b) => Term.tuple [BERT.toTerm a, BERT.toTerm b]

  def pairFromTerm : Term → Sum String (α × β)
  | Term.tuple [a, b] => do
    let x ← BERT.fromTerm a;
    let y ← BERT.fromTerm b;
    pure (x, y)
  | _ => Sum.inl "given BERT term is not a cartesian product"

  instance Prod.BERT : BERT (α × β) := ⟨pairToTerm, pairFromTerm⟩
end

def word : ByteParser UInt16 := do
  let res ← Parser.count Parser.byte 2;
  match res with
  | (a, b, _) =>
    let a' := UInt8.shiftl16 a (8 * 1);
    let b' := UInt8.shiftl16 b (8 * 0);
    pure (a' + b')

def dword : ByteParser UInt32 := do
  let res ← Parser.count Parser.byte 4;
  match res with
  | (a, b, c, d, _) =>
    let a' := UInt8.shiftl32 a (8 * 3);
    let b' := UInt8.shiftl32 b (8 * 2);
    let c' := UInt8.shiftl32 c (8 * 1);
    let d' := UInt8.shiftl32 d (8 * 0);
    pure (a' + b' + c' + d')

-- decode
def readByte : ByteParser Term :=
do Parser.tok 97; let val ← Parser.byte; pure (Term.byte val)

def readDword : ByteParser Term :=
do Parser.tok 98; let res ← dword; pure (Term.int res)

def readASCIIString {α : Type} (p : ByteParser α)
  (toNat : α → Nat) (tok : UInt8) : ByteParser String := do
  Parser.tok tok; let N ← p;
  let chars ← Parser.count ByteParser.ch (toNat N);
  pure chars.toList.asString

def readAtom : ByteParser Term :=
Parser.decorateError "<atom>"
  (Term.atom <$> readASCIIString word UInt16.toNat 100)

def readSmallAtom : ByteParser Term :=
Parser.decorateError "<small atom>"
  (Term.atom <$> readASCIIString Parser.byte UInt8.toNat 115)

def readUTF8String {α : Type} (p : ByteParser α)
  (toNat : α → Nat) (tok : UInt8) : ByteParser String :=
do Parser.tok tok; let N ← p; ByteParser.utf8.stringWithLength (toNat N)

def readUTF8Atom : ByteParser Term :=
Parser.decorateError "<UTF-8 atom>"
  (Term.atom <$> readUTF8String word UInt16.toNat 118)

def readUTF8SmallAtom : ByteParser Term :=
Parser.decorateError "<UTF-8 small atom>"
  (Term.atom <$> readUTF8String Parser.byte UInt8.toNat 119)

def readString : ByteParser Term :=
Parser.decorateError "<UTF-8 string>"
  (Term.string <$> readUTF8String word UInt16.toNat 107)

def readTuple (readTerm : ByteParser Term) : ByteParser Term := do
  Parser.tok 104; let N ← Parser.byte;
  let elems ← Parser.count readTerm N.toNat;
  pure (Term.tuple elems.toList)

def readLargeTuple (readTerm : ByteParser Term) : ByteParser Term := do
  Parser.tok 105; let N ← dword;
  let elems ← Parser.count readTerm N.toNat;
  pure (Term.tuple elems.toList)

def readNil : ByteParser Term := do Parser.tok 106; pure (Term.list [])
def readList (readTerm : ByteParser Term) : ByteParser Term := do
  Parser.tok 108; let N ← dword;
  let elems ← Parser.count readTerm N.toNat;
  let _ ← optional readNil;
  pure (Term.list elems.toList)

def readBinary : ByteParser Term := do
  Parser.tok 109; let N ← dword;
  let elems ← Parser.count Parser.byte N.toNat;
  pure (Term.binary elems.toList.toByteArray)

def IsMinus : ByteParser Bool :=
(do Parser.tok 0; pure false) <|>
(do Parser.tok 1; pure true)

def readBignum' {α : Type}
  (p : ByteParser α) (toNat : α → Nat) (tok : UInt8) :
  ByteParser Term := do
  Parser.tok 110; let n ← p;
  let isMinus ← IsMinus; let d ← Parser.count Parser.byte (toNat n);
  let x := Int.ofNat
    (List.foldl Nat.add 0 $
      List.map (λ (pair : Nat × UInt8) =>
                 pair.2.toNat * (256 ^ pair.1))
               d.toList.enum);
  pure (Term.bigint $ if isMinus then -x else x)

def readSmallBignum := readBignum' Parser.byte UInt8.toNat 110
def readLargeBignum := readBignum' dword UInt32.toNat 111

def readDict (readTerm : ByteParser Term) : ByteParser Term := do
  Parser.tok 116; let L ← dword;
  let pairs ← Parser.count (Prod.mk <$> readTerm <*> readTerm) L.toNat;
  pure (Term.dict pairs.toList)

def readTerm' (readTerm : ByteParser Term) : ByteParser Term :=
readByte <|> readDword <|> readAtom <|>
readUTF8SmallAtom <|> readUTF8Atom <|>
readTuple readTerm <|> readLargeTuple readTerm <|>
readList readTerm <|> readBinary <|> readSmallAtom <|>
readSmallBignum <|> readLargeBignum <|> readString <|>
readDict readTerm

def readTerm : ByteParser Term := do Parser.tok 131; Parser.fix readTerm'

-- encode
partial def natToBytesAux (x : Nat) (buff : ByteArray) : ByteArray :=
if x > 256 then natToBytesAux (x / 256) (buff.push (UInt8.ofNat $ x % 256))
else buff.push (UInt8.ofNat x)

def Nat.toBytes (x : Nat) : ByteArray :=
natToBytesAux x ByteArray.empty

def writeBigint (x : Int) : Put :=
  let enc := Nat.toBytes x.natAbs;
  let sign := if x > 0 then Put.byte 0 else Put.byte 1;
  if enc.size < UInt8.size then
    Put.byte 110 >> Put.byte enc.size >> sign >> Put.tell enc
  else if enc.size < UInt32.size then
    Put.byte 111 >> Put.dword enc.size >> sign >> Put.tell enc
  else Put.fail "BERT integer too big"

def writeAtom (x : String) : Put :=
  if x.utf8ByteSize < UInt8.size then
    if x.all Char.isAscii then
      Put.byte 115 >> Put.byte x.length >> Put.tell x.bytes
    else Put.byte 119 >> Put.byte x.utf8ByteSize >> Put.unicode x
  else if x.utf8ByteSize < UInt16.size then
    if x.all Char.isAscii then
      Put.byte 100 >> Put.word x.length >> Put.tell x.bytes
    else Put.byte 118 >> Put.word x.utf8ByteSize >> Put.unicode x
  else Put.fail "BERT atom too long (≥ 65536)"
  
def writeString (x : String) : Put :=
  if x.utf8ByteSize < UInt16.size then
    Put.byte 107 >> Put.word x.utf8ByteSize >> Put.unicode x
  else Put.fail "BERT bytelist too long (≥ 65536)"

partial def writeTerm' : Term → Put
| Term.byte x => Put.byte 97 >> Put.raw x
| Term.int x => Put.byte 98 >> Put.tell x.toBytes
| Term.atom s => writeAtom s
| Term.tuple x =>
  let tuple := List.foldr (HAndThen.hAndThen ∘ writeTerm') Put.nope;
  if x.length < UInt8.size then
    Put.byte 104 >> Put.byte x.length >> tuple x
  else if x.length < UInt32.size then
    Put.byte 105 >> Put.dword x.length >> tuple x
  else Put.fail "BERT tuple too long (≥ 4294967296)"
| Term.list x =>
  if x.length < UInt32.size then
    Put.byte 108 >> Put.dword x.length >>
    List.foldr (HAndThen.hAndThen ∘ writeTerm') (Put.byte 106) x
  else Put.fail "BERT list too long (≥ 4294967296)"
| Term.binary x =>
  if x.size < UInt32.size then
    Put.byte 109 >> Put.dword x.size >> Put.tell x
  else Put.fail "BERT binary too long (≥ 4294967296)"
| Term.bigint x => writeBigint x
| Term.string s => writeString s
| Term.dict x =>
  let writePair :=
  λ (x : Term × Term) => writeTerm' x.1 >> writeTerm' x.2;
  if x.length < UInt32.size then
    Put.byte 116 >> Put.dword x.length >>
    List.foldr (HAndThen.hAndThen ∘ writePair) Put.nope x
  else Put.fail "BERT dictionary too long (≥ 4294967296)"

def writeTerm (x : Term) : Sum String ByteArray :=
Put.run (Put.byte 131 >> writeTerm' x)

