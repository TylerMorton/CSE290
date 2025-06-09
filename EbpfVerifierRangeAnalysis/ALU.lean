import Std
import Mathlib.Data.Int.Init
import EbpfVerifierRangeAnalysis.Overflow
import EbpfVerifierRangeAnalysis.Register

--- Intro:


-- ** Addition **

-- Definitions
def UInt32_max : UInt32 := UInt32.ofNat (2^32 - 1)
def UInt_max : UInt64 := UInt64.ofNat (2^64 - 1)
def Int32_max : Int32 := Int32.maxValue

@[simp]
def scalar_add_32(a b: BpfRegister) : BpfRegister :=
  let (u32_min, u32_max) := if unsignedCheckAddOverflow32 a.u32_min b.u32_min ∨
    unsignedCheckAddOverflow32 a.u32_max b.u32_max then
    (0, UInt32_max)
    else
    (a.u32_min + b.u32_min, a.u32_max + b.u32_max)

  -- let (s32_min, s32_max) := if signedCheckAddOverflow32 a.s32_min b.s32_min ∨
  --   signedCheckAddOverflow32 a.s32_max b.s32_max then
  --   (0, Int32_max) else
  --   (a.s32_min + b.s32_min, a.s32_max + b.s32_max)

  {
    u32_min := u32_min,
    u32_max := u32_max,
    --s32_min := s32_min,
    --s32_max := s32_max,
    var_off    := a.var_off
  }


@[simp]
def bpf_reg_add(a b : BpfRegister) : BpfRegister :=
  let sum32 := scalar_add_32 a b
  {
    u32_max := sum32.u32_max
    u32_min := sum32.u32_min
    -- s32_max := sum32.s32_max
    --s32_min := sum32.s32_min
    var_off := tnum_add a.var_off b.var_off
  }

-- Proofs
theorem UInt32.le_nat_iff (a b : UInt32) : (a ≤ b) ↔ ((a.toNat : Nat) ≤ (b.toNat : Nat)) := by
  exact UInt32.le_iff_toNat_le

theorem zero_lt_UInt32_max : (0 : UInt32) < UInt32.max := by
  have h := UInt32.lt_iff_toNat_lt 0 UInt32.max
  rw [UInt32.zero] at h
  rw [UInt32.max] at h
  simp only [Nat.zero_lt_succ]
  exact Nat.zero_lt_pow (by decide) 32


lemma UInt32.lt_toNat {a b : UInt32} : a < b ↔ a.toNat < b.toNat := by
  unfold UInt32.instIntCast
  unfold Lt.lt instLTUInt32
  unfold LT.lt instLTUInt32
  unfold UInt32.lt
  simp only [compare, decide_eq_true_eq]
  cases h : compare a b
  case lt => simp [compare, h]
  case eq => simp [compare, h]
  case gt => simp [compare, h]

theorem scalar_add_32_range_bounds
  (a b : BpfRegister)
  (ha : a.u32_min < a.u32_max)
  (hb : b.u32_min < b.u32_max)
  : let c := scalar_add_32 a b
    c.u32_min < c.u32_max :=
  by
    let c := scalar_add_32 a b
    let overflow := unsignedCheckAddOverflow32 a.u32_min b.u32_min || unsignedCheckAddOverflow32 a.u32_max b.u32_max
    by_cases h_overflow : overflow
    · unfold scalar_add_32
      split_ifs with h
      ·  simp [UInt32_max]
    · unfold scalar_add_32
      split_ifs with h
      · simp [scalar_add_32, h_overflow]
        rw [UInt32_max]
      · simp [scalar_add_32, h_overflow]
        rw [UInt32.lt_iff_toNat_lt] at ha
        rw [UInt32.lt_iff_toNat_lt] at hb
        exact Nat.add_lt_add ha hb

    exact Nat.zero_le (UInt32_max.toNat)


-- Subtraction
