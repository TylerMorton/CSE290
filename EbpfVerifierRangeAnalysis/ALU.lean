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

-- TODO: Version 1
-- @[simp]
-- theorem scalar_add_32_bounds_max (a b : BpfRegister) :
--   (scalar_add_32 a b).u32_max ≥  a.u32_max ∧ (scalar_add_32 a b).u32_max ≥ b.u32_max := by
--   unfold scalar_add_32
--   split_ifs with h
--   · simp
--     split_ands
--     · unfold UInt32_max
--       have h : a.u32_max.toNat ≤ 2^32 - 1 := Nat.le_pred_of_lt (UInt32.toNat_lt a.u32_max)
--       apply h
--     · unfold UInt32_max
--       have h : b.u32_max.toNat ≤ 2^32 - 1 := Nat.le_pred_of_lt (UInt32.toNat_lt b.u32_max)
--       apply h
--   · simp
--     split_ands
--     -- ·  have h : a.u32_max ≤ a.u32_max + b.u32_max :=
--     -- · unfold UInt32_max
--     --   have h : b.u32_max.toNat ≤ 2^32 - 1 := Nat.le_pred_of_lt (UInt32.toNat_lt b.u32_max)
--     --   apply h
--     · sorry
--     · sorry

-- TODO: Version 2
-- @[simp]
-- theorem scalar_add_32_bounds_max (a b : BpfRegister) :
--   (scalar_add_32 a b).u32_max ≥  a.u32_max + b.u32_max := by
--   unfold scalar_add_32
--   split_ifs with h
--   · simp
--     unfold UInt32_max
--     simp
--     have h : a.u32_max.toNat + b.u32_max.toNat ≤ 2^32 - 1 := Nat.le_pred_of_lt (UInt32.toNat_lt a.u32_max)
--     split_ands
--     · unfold UInt32_max
--       have h : a.u32_max.toNat ≤ 2^32 - 1 := Nat.le_pred_of_lt (UInt32.toNat_lt a.u32_max)
--       apply h
--     · unfold UInt32_max
--       have h : b.u32_max.toNat ≤ 2^32 - 1 := Nat.le_pred_of_lt (UInt32.toNat_lt b.u32_max)
--       apply h
--   · simp
--     split_ands
--     -- ·  have h : a.u32_max ≤ a.u32_max + b.u32_max :=
--     -- · unfold UInt32_max
--     --   have h : b.u32_max.toNat ≤ 2^32 - 1 := Nat.le_pred_of_lt (UInt32.toNat_lt b.u32_max)
--     --   apply h
--     · sorry
--     · sorry

@[simp]
theorem scalar_add_32_bounds_max (a b : BpfRegister) :
  (scalar_add_32 a b).u32_max ≥  a.u32_max + b.u32_max:= by
  sorry



theorem scalar_add_32_bounds ( a b : BpfRegister) :
  ((scalar_add_32 a b).u32_min ≤ a.u32_min + b.u32_min) ∧
  ((scalar_add_32 a b).u32_max ≥ a.u32_max + b.u32_max) ∧
  ((scalar_add_32 a b).u32_max ≥ (scalar_add_32 a b).u32_min)
   := by
  split_ands
  · simp
  · simp
  · unfold scalar_add_32
    simp
    split
    · simp
    · sorry -- :(
  -- · apply scalar_add_32_bounds_min
  -- · apply scalar_add_32_bounds_max


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



theorem UInt32.add_lt_add {a b c d : UInt32} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  UInt32.lt_trans (UInt32.add_lt_add_right h₁ c) (UInt32.add_lt_add_left h₂ b)

theorem UInt32.add_lt_add_right {a b : UInt32} (h: a < b) (k : UInt32) : a + k < b + k :=
  UInt32.add_comm k b ▸ UInt32.add_comm k a ▸ UInt32.add_lt_addleft


theorem UInt32.add_lt_add_left {a b : UInt32}
(h: a.toNat < b.toNat) (k: UInt32)
(h1: (a.toNat + k.toNat) < 2^32)
(h2: (b.toNat + k.toNat) < 2^32):
(a + k).toNat < (b + k).toNat := by
have ha' : (a + k).toNat = a.toNat + k.toNat := UInt32.toNat_add_ofNat h1

simp [add, instAddUInt32]
simp [add, UInt32.add, OfNat.ofNat, UInt32.ofNat, UInt32.toNat]


@[simp]
lemma Nat.lt_add_lt_int_if {a b : UInt32} (h : a < b) : (a.toNat : Nat) < (b.toNat : Nat) := by
  exact UInt32.lt_iff_toNat_lt.mp h

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
        simp
      · simp [scalar_add_32, h_overflow]
        rw [UInt32.lt_iff_toNat_lt] at ha
        rw [UInt32.lt_iff_toNat_lt] at hb
        have h1 : a.u32_min.toNat < a.u32_max.toNat := Nat.lt_add_lt_int_if ha
        have h2 : b.u32_min.toNat < b.u32_max.toNat := Nat.lt_add_lt_int_if hb
        have h3 : Nat.add_lt_add (a.u32_min.toNat < a.u32_max.toNat) (b.u32_min.toNat < b.u32_max.toNat)
have sum_lt : x1.toNat + x2.toNat < y1.toNat + y2.toNat := Nat.add_lt_add h1 h2

        have ha' := Nat.lt_add_lt_int_if ha
        have hb' := Nat.lt_add_lt_int_if hb
        simp
        exact Nat.add_lt_add ha' hb'

    exact Nat.zero_le (UInt32_max.toNat)


-- Subtraction
