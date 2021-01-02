@[extern c inline "#1 << #2"]
constant UInt8.shiftl (a b : UInt8) : UInt8
@[extern c inline "#1 >> #2"]
constant UInt8.shiftr (a b : UInt8) : UInt8

@[extern c inline "#1 << #2"]
constant UInt16.shiftl (a b : UInt16) : UInt16
@[extern c inline "#1 >> #2"]
constant UInt16.shiftr (a b : UInt16) : UInt16

@[extern c inline "#1 << #2"]
constant UInt32.shiftl (a b : UInt32) : UInt32
@[extern c inline "#1 >> #2"]
constant UInt32.shiftr (a b : UInt32) : UInt32

@[extern c inline "((uint16_t) #1)"]
def UInt8.toUInt16 (x : UInt8) : UInt16 := x.toNat.toUInt16
@[extern c inline "((uint8_t) #1)"]
def UInt16.toUInt8 (x : UInt16) : UInt8 := x.toNat.toUInt8

def UInt16.nthByte (x : UInt16) (n : Nat) : UInt8 :=
(UInt16.land (UInt16.shiftr x $ 8 * UInt16.ofNat n) 255).toUInt8

def UInt32.nthByte (x : UInt32) (n : Nat) : UInt8 :=
(UInt32.land (UInt32.shiftr x $ 8 * UInt32.ofNat n) 255).toUInt8

def iotaZero : Nat → List Nat
|   0   => [0]
| n + 1 => (n + 1) :: iotaZero n

def UInt16.toBytes (x : UInt16) : ByteArray :=
List.toByteArray (List.map (UInt16.nthByte x) (iotaZero 1))

def UInt32.toBytes (x : UInt32) : ByteArray :=
List.toByteArray (List.map (UInt32.nthByte x) (iotaZero 3))

def UInt8.shiftl16 (x : UInt8) (y : UInt16) : UInt16 :=
UInt16.shiftl x.toUInt16 y

def UInt8.shiftl32 (x : UInt8) (y : UInt32) : UInt32 :=
UInt32.shiftl x.toUInt32 y

def String.bytes (x : String) : ByteArray :=
List.toByteArray (List.map (UInt8.ofNat ∘ Char.toNat) x.toList)
