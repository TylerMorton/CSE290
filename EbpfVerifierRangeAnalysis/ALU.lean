import Std
import Mathlib.Data.Int.Init
import EbpfVerifierRangeAnalysis.Overflow
import EbpfVerifierRangeAnalysis.Register

--- Intro:


-- ** Addition **

-- Definitions

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
theorem scalar_add_32_bounds_min (a b : BpfRegister) :
  (scalar_add_32 a b).u32_min ≤  a.u32_min + b.u32_min := by
  unfold scalar_add_32
  split_ifs with h
  · simp
  · simp

-- TODO: Version 2
@[simp]
theorem scalar_add_32_bounds_max (a b : BpfRegister) :
  (scalar_add_32 a b).u32_max ≥  a.u32_max + b.u32_max := by
  unfold scalar_add_32
  split_ifs with h
  · simp
    unfold UInt32_max
    simp
    bv_decide
  · simp

theorem scalar_add_32_bounds ( a b : BpfRegister) :
  ((scalar_add_32 a b).u32_min ≤ a.u32_min + b.u32_min) ∧
  ((scalar_add_32 a b).u32_max ≥ a.u32_max + b.u32_max) ∧
  ((scalar_add_32 a b).u32_max ≥ (scalar_add_32 a b).u32_min)
   := by
  split_ands
  · simp -- sum is le added components (modulo) (bounds_min)
  · simp -- sum is ge added components (modulo) (bounds_max)
  ·      -- max is always ge min
    unfold scalar_add_32
    simp
    split_ifs
    · simp -- overflow occurs
    · simp -- this case is strange
      -- bv_decide
      sorry -- :(

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

@[simp]
lemma Nat.lt_add_lt_int_if {a b : UInt32} (h : a < b) : (a.toNat : Nat) < (b.toNat : Nat) := by
  exact UInt32.lt_iff_toNat_lt.mp h


-- Subtraction
