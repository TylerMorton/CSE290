import Std
import Mathlib.Data.Int.Init
import Mathlib.Data.Nat.ModEq
import EbpfVerifierRangeAnalysis.Overflow
import EbpfVerifierRangeAnalysis.Register

--- Intro:

-- **Addition**

lemma uint32_aux {a b a' b' : UInt32} (h : a.toNat + b.toNat < UInt32.size) (h' : a'.toNat + b'.toNat < UInt32.size)
    (hn : a.toNat + b.toNat ≤ a'.toNat + b'.toNat) :
    a + b ≤ a' + b' := by
  change (a + b).toNat ≤ (a' + b').toNat
  simp only [UInt32.toNat_add]
  rw [Nat.add_mod_of_add_mod_lt, Nat.add_mod_of_add_mod_lt]
  · simpa using hn
  · simpa using h'
  · simpa using h

lemma uint64_aux {a b a' b' : UInt64} (h : a.toNat + b.toNat < UInt64.size) (h' : a'.toNat + b'.toNat < UInt64.size)
    (hn : a.toNat + b.toNat ≤ a'.toNat + b'.toNat) :
    a + b ≤ a' + b' := by
  change (a + b).toNat ≤ (a' + b').toNat
  simp only [UInt64.toNat_add]
  rw [Nat.add_mod_of_add_mod_lt, Nat.add_mod_of_add_mod_lt]
  · simpa using hn
  · simpa using h'
  · simpa using h


def scalar_add_32(a b : BpfRegister) : BpfRegister :=
-- pattern matching (have v let)
  let u32_res := if unsignedCheckAddOverflow32 a.u32_min b.u32_min ∨
    unsignedCheckAddOverflow32 a.u32_max b.u32_max then
    (0, UInt32_max)
    else
    (a.u32_min + b.u32_min, a.u32_max + b.u32_max)
  let u64_res := if unsignedCheckAddOverflow a.u64_min b.u64_min ∨
    unsignedCheckAddOverflow a.u64_max b.u64_max then
    (0, UInt_max)
    else
    (a.u64_min + b.u64_min, a.u64_max + b.u64_max)
  {
    u32_min := u32_res.1,
    u32_max := u32_res.2,
    u32_well_formed := by
      revert u32_res
      split_ifs
      · simp
      · simp
        rename_i h
        simp at h
        apply uint32_aux
        · simp [UInt32.size]
          omega
        · simp [UInt32.size]
          omega
        · exact Nat.add_le_add a.u32_well_formed b.u32_well_formed,
      u64_min := a.u64_min,
      u64_max := a.u64_max,
      u64_well_formed := a.u64_well_formed
    var_off    := a.var_off
  }

def scalar_add(a b : BpfRegister) : BpfRegister :=
-- pattern matching (have v let)
  let u64_res := if unsignedCheckAddOverflow a.u64_min b.u64_min ∨
    unsignedCheckAddOverflow a.u64_max b.u64_max then
    (0, UInt_max)
    else
    (a.u64_min + b.u64_min, a.u64_max + b.u64_max)
  {
    u32_min := a.u32_min
    u32_max := a.u32_max
    u32_well_formed := a.u32_well_formed
    u64_min := u64_res.1,
    u64_max := u64_res.2,
    u64_well_formed := by
      revert u64_res
      split_ifs
      · simp
      · simp
        rename_i h
        simp at h
        apply uint64_aux
        · simp [UInt64.size]
          omega
        · simp [UInt64.size]
          omega
        · exact Nat.add_le_add a.u64_well_formed b.u64_well_formed
    var_off    := a.var_off
  }

theorem scalar_add_32_bounds_min (a b : BpfRegister) :
  (scalar_add_32 a b).u32_min ≤  a.u32_min + b.u32_min := by
  unfold scalar_add_32
  simp
  split_ifs with h
  · simp
  · simp

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

theorem scalar_add_32_bounds_well_formed (a b: BpfRegister) :
  ((scalar_add_32 a b).u32_max ≥ (scalar_add_32 a b).u32_min) := by
  apply BpfRegister.u32_well_formed

theorem scalar_add_64_bounds_min (a b : BpfRegister) :
  (scalar_add a b).u64_min ≤  a.u64_min + b.u64_min := by
  unfold scalar_add
  simp
  split_ifs with h
  · simp
  · simp

theorem scalar_add_64_bounds_max (a b : BpfRegister) :
  (scalar_add a b).u64_max ≥  a.u64_max + b.u64_max := by
  unfold scalar_add
  simp
  split_ifs with h
  · simp
    unfold UInt_max
    simp
    bv_decide
  · simp

theorem scalar_add_bounds_well_formed (a b: BpfRegister) :
  ((scalar_add a b).u64_max ≥ (scalar_add a b).u64_min) := by
  apply BpfRegister.u64_well_formed
