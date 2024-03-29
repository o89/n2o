def UInt16.nthByte (x : UInt16) (n : Nat) : UInt8 :=
(UInt16.land (x.shiftRight $ 8 * UInt16.ofNat n) 255).toUInt8

def UInt32.nthByte (x : UInt32) (n : Nat) : UInt8 :=
(UInt32.land (x.shiftRight $ 8 * UInt32.ofNat n) 255).toUInt8

def iotaZero : Nat → List Nat
|   0   => [0]
| n + 1 => (n + 1) :: iotaZero n

def UInt16.toBytes (x : UInt16) : ByteArray :=
List.toByteArray (List.map (UInt16.nthByte x) (iotaZero 1))

def UInt32.toBytes (x : UInt32) : ByteArray :=
List.toByteArray (List.map (UInt32.nthByte x) (iotaZero 3))

def UInt8.shiftl16 (x : UInt8) (y : UInt16) : UInt16 :=
UInt16.shiftRight x.toUInt16 y

def UInt8.shiftl32 (x : UInt8) (y : UInt32) : UInt32 :=
UInt32.shiftRight x.toUInt32 y

def String.bytes (x : String) : ByteArray :=
List.toByteArray (List.map (UInt8.ofNat ∘ Char.toNat) x.toList)
