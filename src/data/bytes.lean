@[extern c inline "#1 << #2"]
constant UInt8.shiftl (a b : UInt8) : UInt8 := UInt8.ofNat (default _)
@[extern c inline "#1 >> #2"]
constant UInt8.shiftr (a b : UInt8) : UInt8 := UInt8.ofNat (default _)

@[extern c inline "#1 << #2"]
constant UInt16.shiftl (a b : UInt16) : UInt16 := UInt16.ofNat (default _)
@[extern c inline "#1 >> #2"]
constant UInt16.shiftr (a b : UInt16) : UInt16 := UInt16.ofNat (default _)

@[extern c inline "#1 << #2"]
constant UInt32.shiftl (a b : UInt32) : UInt32 := UInt32.ofNat (default _)
@[extern c inline "#1 >> #2"]
constant UInt32.shiftr (a b : UInt32) : UInt32 := UInt32.ofNat (default _)

def UInt8.toUInt32 (x : UInt8) : UInt32 := UInt32.ofNat x.toNat
def UInt16.crop (x : UInt16) : UInt8 := UInt8.ofNat x.toNat
def UInt32.crop (x : UInt32) : UInt8 := UInt8.ofNat x.toNat

def UInt16.nthByte (x : UInt16) (n : Nat) : UInt8 :=
(UInt16.land (UInt16.shiftr x $ 8 * UInt16.ofNat n) 255).crop

def UInt32.nthByte (x : UInt32) (n : Nat) : UInt8 :=
(UInt32.land (UInt32.shiftr x $ 8 * UInt32.ofNat n) 255).crop

def List.iotaZero : Nat → List Nat
| 0     ⇒ [ 0 ]
| n + 1 ⇒ (n + 1) :: List.iotaZero n

def UInt16.toBytes (x : UInt16) : ByteArray :=
List.toByteArray $ UInt16.nthByte x <$> List.iotaZero 1

def UInt32.toBytes (x : UInt32) : ByteArray :=
List.toByteArray $ UInt32.nthByte x <$> List.iotaZero 3

def UInt8.shiftl16 (x : UInt8) (y : UInt16) : UInt16 :=
UInt16.shiftl (UInt16.ofNat x.toNat) y

def UInt8.shiftl32 (x : UInt8) (y : UInt32) : UInt32 :=
UInt32.shiftl (UInt32.ofNat x.toNat) y

partial def ByteArray.appendAux : Nat → ByteArray → ByteArray → ByteArray
| i, dest, res ⇒
  if i < res.size then ByteArray.appendAux (i + 1) (dest.push $ res.get i) res
  else dest

def ByteArray.append := ByteArray.appendAux 0
instance : HasAppend ByteArray := ⟨ByteArray.append⟩

def String.bytes (x : String) : ByteArray :=
List.toByteArray $ (UInt8.ofNat ∘ Char.toNat) <$> x.toList
