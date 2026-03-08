import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000 -- scalr_tac exceeds standard heartbeats rates
set_option exponentiation.threshold 500

/-! # MulInternal

The main statement concerning `mul_internal` is `mul_internal_spec` (below).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `mul_internal` -/

/-- **Spec for `backend.serial.u64.scalar.Scalar52.mul_internal`**:
- The result represents the product of the two input field elements
- Requires that each input limb is at most 62 bits to prevent overflow -/
@[progress]
theorem mul_internal_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62) :
    mul_internal a b ⦃ (result : Array U128 9#usize) =>
      Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat b ∧
      (∀ i < 9, result[i]!.val < 2 ^ 127) ⦄ := by
  unfold mul_internal
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  progress*
  constructor
  · simp [*, Scalar52_wide_as_Nat, Scalar52_as_Nat, Finset.sum_range_succ]
    ring
  · intro i hi
    have := ha 0 (by simp); have := hb 0 (by simp)
    have := ha 1 (by simp); have := hb 1 (by simp)
    have := ha 2 (by simp); have := hb 2 (by simp)
    have := ha 3 (by simp); have := hb 3 (by simp)
    have := ha 4 (by simp); have := hb 4 (by simp)
    interval_cases i
    all_goals simp [*]; grind

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
