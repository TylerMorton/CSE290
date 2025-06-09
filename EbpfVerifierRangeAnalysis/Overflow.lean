import Mathlib.Data.Int.Init

@[simp]
def unsignedCheckAddOverflow32 (a b : UInt32) : Bool :=
  let sum := a.toNat + b.toNat
  sum ≥ UInt32.size

@[simp]
def signedCheckAddOverflow32 (a b : Int32): Bool :=
  let sum := a.toNat + b.toNat
  sum ≥ Int32.size

@[simp]
def unsignedCheckAddOverflow(a b : UInt64) : Bool :=
  let sum := a.toNat + b.toNat
  sum ≥ UInt64.size

@[simp]
def signedCheckAddOverflow (a b : Int64) : Bool :=
  let sum := a.toNat + b.toNat
  sum ≥ UInt64.size
