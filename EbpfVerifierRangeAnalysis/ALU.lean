import Std
import Mathlib.Data.Int.Init
import Mathlib.Data.Nat.ModEq
import EbpfVerifierRangeAnalysis.Overflow
import EbpfVerifierRangeAnalysis.Register

--- Intro:

-- **Addition**



lemma aux {a b a' b' : UInt32} (h : a.toNat + b.toNat < UInt32.size) (h' : a'.toNat + b'.toNat < UInt32.size)
    (hn : a.toNat + b.toNat ≤ a'.toNat + b'.toNat) :
    a + b ≤ a' + b' := by
  change (a + b).toNat ≤ (a' + b').toNat
  simp only [UInt32.toNat_add]
  rw [Nat.add_mod_of_add_mod_lt, Nat.add_mod_of_add_mod_lt]
  · simpa using hn
  · simpa using h'
  · simpa using h


def scalar_add_32(a b: BpfRegister) : BpfRegister :=
-- pattern matching (have v let)
  let res := if unsignedCheckAddOverflow32 a.u32_min b.u32_min ∨
    unsignedCheckAddOverflow32 a.u32_max b.u32_max then
    (0, UInt32_max)
    else
    (a.u32_min + b.u32_min, a.u32_max + b.u32_max)
  {
    u32_min := res.1,
    u32_max := res.2,
    well_formed := by
      revert res
      split_ifs
      · simp
      · simp
        rename_i h
        simp at h
        apply aux
        · simp [UInt32.size]
          omega
        · simp [UInt32.size]
          omega
        · exact Nat.add_le_add a.well_formed b.well_formed
    var_off    := a.var_off
  }

@[simp]
theorem scalar_add_32_bounds_min (a b : BpfRegister) :
  (scalar_add_32 a b).u32_min ≤  a.u32_min + b.u32_min := by
  unfold scalar_add_32
  simp
  split_ifs with h
  · simp
  · simp

@[simp]
theorem scalar_add_32_bounds_max (a b : BpfRegister) :
  (scalar_add_32 a b).u32_max ≥  a.u32_max + b.u32_max := by
  unfold scalar_add_32
  simp
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
  · apply BpfRegister.well_formed     -- max is always ge min
