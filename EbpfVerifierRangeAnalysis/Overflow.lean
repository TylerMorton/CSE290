import Mathlib.Data.Int.Init

def UInt32_max : UInt32 := UInt32.ofNat (2^32 - 1)
def UInt_max : UInt64 := UInt64.ofNat (2^64 - 1)
def Int32_max : Int32 := Int32.maxValue
def Int_max : Int64 := Int64.maxValue

@[simp]
def unsignedCheckAddOverflow32 (a b : UInt32) : Bool :=
  let sum := a.toNat + b.toNat
  sum ≥ UInt32_max

@[simp]
def signedCheckAddOverflow32 (a b : Int32): Bool :=
  let sum := a.toNat + b.toNat
  sum ≥ Int32_max

@[simp]
def unsignedCheckAddOverflow(a b : UInt64) : Bool :=
  let sum := a.toNat + b.toNat
  sum ≥ UInt_max

@[simp]
def signedCheckAddOverflow (a b : Int64) : Bool :=
  let sum := a.toNat + b.toNat
  sum ≥ Int_max
