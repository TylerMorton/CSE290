import Mathlib.Data.Int.Init
import Mathlib.Algebra.Algebra.Subalgebra.Order
import Std

structure tnum where
  value : UInt64
  mask : UInt64


def well_formed_tnum {α : Type} [AndOp α] [OfNat α 0] [BEq α] (mask value : α ) : Prop :=
  mask &&& value = 0

def contains_tnum {α : Type} [Complement α] [AndOp α] [Xor α] [OfNat α 0] (mask value s : α): Prop :=
  ((~~~mask) &&& (value ^^^ s)) = 0


@[simp]
def tnum_add (a b : tnum) : tnum :=
  let sm := a.mask + b.mask
  let sv := a.value + b.value
  let sigma := sm + sv
  let chi := UInt64.xor sigma  sv
  let mu := chi ||| a.mask ||| b.mask
  { value := sv &&& ~~~mu, mask := mu }

theorem tnum_add_value_and_mask_zero (a b : tnum) :
  let result := tnum_add a b
  result.value &&& result.mask = 0 :=
by
  unfold tnum_add
  simp
  let sm := a.mask + b.mask
  let sv := a.value + b.value
  let sigma := sm + sv
  let chi := sigma.xor sv
  let mu := chi ||| a.mask ||| b.mask
  let v := sv &&& ~~~mu
  have h_v_and_mu: v &&& mu = 0 := by
    unfold v
    rw [UInt64.and_assoc]
    rw [UInt64.not_and_self]
    rw [ UInt64.and_zero]

  exact h_v_and_mu
