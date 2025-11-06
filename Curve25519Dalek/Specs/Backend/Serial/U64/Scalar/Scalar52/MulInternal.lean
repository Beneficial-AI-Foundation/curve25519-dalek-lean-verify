import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Defs
import Curve25519Dalek.Tactics
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 500

/-! # MulInternal

The main statement concerning `mul_internal` is `mul_internal_spec` (below).
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `mul_internal` -/

/-- **Spec for `backend.serial.u64.scalar.Scalar52.mul_internal`**:
- Does not error and hence returns a result
- The result represents the product of the two input field elements
- Requires that each input limb is at most 62 bits to prevent overflow -/
@[progress]
theorem mul_internal_spec (a b : Array U64 5#usize)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62)
    (hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 62) :
    ∃ result, mul_internal a b = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat b := by
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
