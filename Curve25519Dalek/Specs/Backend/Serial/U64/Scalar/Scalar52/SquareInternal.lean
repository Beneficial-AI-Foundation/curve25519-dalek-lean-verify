import Curve25519Dalek.Defs
import Curve25519Dalek.Tactics
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 500


/-! # SquareInternal

The main statement concerning `square_internal` is `square_internal_spec` (below).
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `square_internal` -/

/-- **Spec for `square_internal`**:
- Does not error and hence returns a result
- The result represents the square of the input field element
- Requires each limb to be less than 62 bits to prevent overflow
(The optimal bound on the limbs is 2^64 / √5  ≈ 2^62.839) -/
@[progress]
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
  unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  progress*
  all_goals try subst_vars; expand ha with 5; scalar_tac
  unfold Array.make at *
  simp [Scalar52_wide_as_Nat, Scalar52_as_Nat, Finset.sum_range_succ, *]
  grind

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
