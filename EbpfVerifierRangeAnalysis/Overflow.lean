import Mathlib.Data.Int.Init

def UInt32_max : UInt32 := UInt32.ofNat (2^32 - 1)
def UInt_max : UInt64 := UInt64.ofNat (2^64 - 1)
def Int32_max : Int32 := Int32.maxValue
def Int_max : Int64 := Int64.maxValue


def unsignedCheckAddOverflow32 (a b : UInt32) : Bool :=
  let sum := a.toNat + b.toNat
  sum > UInt32_max.toNat

@[simp]
theorem unsignedCheckAddOverflow32_iff (a b : UInt32) :
  unsignedCheckAddOverflow32 a b ↔ a.toNat + b.toNat > 2^32 - 1 := by
  unfold unsignedCheckAddOverflow32
  simp
  unfold UInt32_max
  simp


def signedCheckAddFlows32 (a b : Int32): Bool :=
  let sum := a.toInt + b.toInt
  sum > Int32_max.toInt ∨ sum < 0

@[simp]
theorem signedCheckAddFlows32_iff (a b : Int32):
  signedCheckAddFlows32 a b ↔
  (a.toInt + b.toInt > Int32.maxValue.toInt) ∨
  (a.toInt + b.toInt < 0):= by
  unfold signedCheckAddFlows32
  simp
  unfold Int32_max
  unfold Int32.maxValue
  simp

def unsignedCheckAddOverflow(a b : UInt64) : Bool :=
  let sum := a.toNat + b.toNat
  sum > UInt_max.toNat

@[simp]
theorem unsignedCheckAddOverflow_iff (a b : UInt64) :
  unsignedCheckAddOverflow a b ↔ a.toNat + b.toNat > 2^64 - 1 := by
  unfold unsignedCheckAddOverflow
  simp
  unfold UInt_max
  simp

def signedCheckAddFlows (a b : Int64) : Bool :=
  let sum := a.toInt + b.toInt
  sum > Int_max.toInt ∨ sum < 0

@[simp]
theorem signedCheckAddOverflow_iff (a b : Int64) :
  signedCheckAddFlows a b ↔
  (a.toInt + b.toInt > Int64.maxValue.toInt) ∨
  (a.toInt + b.toInt < 0) := by
  unfold  signedCheckAddFlows
  simp
  unfold Int_max
  unfold Int64.maxValue
  simp
