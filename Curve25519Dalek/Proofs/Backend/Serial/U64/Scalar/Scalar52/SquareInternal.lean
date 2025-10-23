import Curve25519Dalek.Proofs.Defs
import Curve25519Dalek.Proofs.Backend.Serial.U64.Scalar.M

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

/- Using the specs with bit-vectors -/
-- attribute [-progress] U64.add_spec U64.mul_spec U128.add_spec U128.mul_spec
-- attribute [local progress] U64.add_bv_spec U64.mul_bv_spec U128.add_bv_spec U128.mul_bv_spec
attribute [progress] m_spec

/-- **Spec for `square_internal`**:
- Does not error and hence returns a result
- The result represents the square of the input field element
- Requires each limb to be less than 62 bits to prevent overflow
(The optimal bound on the limbs is 2^64 / √5  ≈ 2^62.839) -/
theorem square_internal_spec (a : Array U64 5#usize)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    U128x9_as_Nat result = U64x5_as_Nat a * U64x5_as_Nat a := by
  unfold square_internal
  unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  progress*
  all_goals try {
    subst_vars
    have := ha 0 (by omega)
    have := ha 1 (by omega)
    have := ha 2 (by omega)
    have := ha 3 (by omega)
    have := ha 4 (by omega)
    scalar_tac
  }
  -- remains to show that `U128x9_as_Nat result = U64x5_as_Nat a * U64x5_as_Nat a`
  unfold Array.make at *
  simp [U128x9_as_Nat, U64x5_as_Nat, Finset.sum_range_succ, *]
  simp_all;
  ring

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
