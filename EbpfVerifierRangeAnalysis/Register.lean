import Std
import EbpfVerifierRangeAnalysis.Tnum

structure BpfRegister where
  -- 32 bit
  u32_min : UInt32
  u32_max: UInt32
  -- s32_min : Int32
  -- s32_max: Int32
  -- 64 bit
  --u64_min: UInt64
  --u64_max: UInt64
  --s64_min : Int64
  --s64_max: Int64
  -- tnum
  var_off: tnum

-- def tnum_known_collapse(reg: BpfRegister) : Prop :=
--   (reg.var_off.mask = 0 →
--     (↑reg.s64_min = ↑ reg.s64_max ∧
--     ↑reg.u64_max = ↑reg.u64_min))

def well_formed_min_max_int32 (min max : Int32) : Prop := min ≤ max
def well_formed_min_max_uint32 (min max : UInt32) : Prop := min ≤ max
def well_formed_min_max_int64 (min max : Int64) : Prop := min ≤ max
def well_formed_min_max_uint64 (min max : UInt64) : Prop := min ≤ max

-- def well_formed_range (reg_state : BpfRegister)
--  : Prop :=
--   well_formed_min_max_int32 reg_state.s32_min reg_state.s32_max ∧
--   well_formed_min_max_uint32 reg_state.u32_min reg_state.u32_max ∧
--   well_formed_min_max_int64 reg_state.s64_min reg_state.s64_max ∧
  -- well_formed_min_max_uint64 reg_state.u64_min reg_state.u64_max


-- Correctness definitions
def contains_min_max {α : Type} [LE α] (min max s : α) : Prop :=
  min ≤ s ∧ s ≤ max


def Int64.toUInt32 (x : Int64) : UInt32 :=
  UInt32.ofNat (x.toNat ^ (2^32))

-- def contains_range(reg_state: BpfRegister) (s: Int64) : Prop :=
--   contains_min_max reg_state.s32_min reg_state.s32_max (Int64.toInt32 s) ∧
--   contains_min_max reg_state.u32_min reg_state.u32_max (Int64.toUInt32 s) ∧
--   contains_min_max reg_state.s64_min reg_state.s64_max s ∧
--   contains_min_max reg_state.u64_min reg_state.u64_max (Int64.toUInt64 s) ∧
--   contains_tnum  reg_state.var_off.mask reg_state.var_off.value (Int64.toUInt64 s)
