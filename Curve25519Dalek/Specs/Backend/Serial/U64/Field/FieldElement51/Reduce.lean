import Curve25519Dalek.Defs

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000

/-! # Reduce

The main statement concerning `reduce` is `reduce_spec` (below).
-/

open Aeneas.Std Result
open curve25519_dalek
open backend.serial.u64.field.FieldElement51
open reduce

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for LOW_51_BIT_MASK -/

theorem LOW_51_BIT_MASK_val_eq : LOW_51_BIT_MASK.val = 2^51 - 1 := by
  unfold LOW_51_BIT_MASK; decide

/-- Bitwise AND with (2^51 - 1) keeps only the lower 51 bits so bounded ≤ 2^51 - 1 < 2^51. -/
theorem and_LOW_51_BIT_MASK_lt (a : U64) : (a &&& LOW_51_BIT_MASK).val < 2^51 := by
  simp [LOW_51_BIT_MASK_val_eq]; omega



/- The `scalar_tac_simps` is important in particular for `scalar_tac` to know
   about this constant (otherwise it treats it as an opaque definition). -/
attribute [simp, scalar_tac_simps] LOW_51_BIT_MASK_val_eq

/- Using the specs with bit-vectors -/
attribute [-progress] U64.add_spec U64.mul_spec
attribute [local progress] U64.add_bv_spec U64.mul_bv_spec


/-! ## Spec for `reduce` -/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.reduce`**:
- Does not overflow and hence returns a result
- All the limbs of the result are small, ≤ 2^(51 + ε)
- The result is equal to the input mod p. -/
@[progress]
theorem reduce_spec (limbs : Array U64 5#usize) :
    ∃ result, reduce limbs = ok (result) ∧
    (∀ i, i < 5 → (result[i]!).val ≤ 2^51 + (2^13 - 1) * 19) ∧
    Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p] := by
  unfold reduce
  progress*
  all_goals try simp [*]; scalar_tac
  constructor
  · intro i _
    interval_cases i
    all_goals simp [*]; scalar_tac
  · simp [Field51_as_Nat, Finset.sum_range_succ, p, Nat.ModEq, *]; omega
