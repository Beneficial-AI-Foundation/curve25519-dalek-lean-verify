import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
import Mathlib.Tactic.IntervalCases

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000

/-! # Reduce -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `reduce` -/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

@[progress]
theorem LOW_51_BIT_MASK_spec :
    LOW_51_BIT_MASK ⦃ result => result.val = 2^51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK
  progress*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.reduce`**:
- All the limbs of the result are small, ≤ 2^(51 + ε)
- The result is equal to the input mod p. -/
@[progress]
theorem reduce_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (result : FieldElement51) =>
      (∀ i < 5, result[i]!.val ≤ 2 ^ 52) ∧
      Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p] ⦄ := by
  unfold reduce
  progress*
  · scalar_tac
  · simp [*]; scalar_tac
  · simp [*]; scalar_tac
  · simp [*]; scalar_tac
  · simp [*]; scalar_tac
  · simp [*]; scalar_tac
  · constructor
    · intro i _
      interval_cases i
      all_goals simp [*]; scalar_tac
    · simp [Field51_as_Nat, Finset.sum_range_succ, p, Nat.ModEq, *]; omega

end curve25519_dalek.backend.serial.u64.field.FieldElement51
