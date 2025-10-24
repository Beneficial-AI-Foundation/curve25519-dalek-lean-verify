import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Defs
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

/- Using the specs with bit-vectors -/
-- attribute [-progress] U64.add_spec U64.mul_spec U128.add_spec U128.mul_spec
-- attribute [local progress] U64.add_bv_spec U64.mul_bv_spec U128.add_bv_spec U128.mul_bv_spec
attribute [progress] m_spec

/-- **Spec for `backend.serial.u64.scalar.Scalar52.mul_internal`**:
- Does not error and hence returns a result
- The result represents the product of the two input field elements
- Requires that each input limb is at most 62 bits to prevent overflow -/
theorem mul_internal_spec (a b : Array U64 5#usize)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62)
    (hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 62) :
    ∃ result, mul_internal a b = ok (result) ∧
    U128x9_as_Nat result = U64x5_as_Nat a * U64x5_as_Nat b := by
  unfold mul_internal
  unfold backend.serial.u64.scalar.Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  -- simp only [Array.getElem!_Nat_eq]
  have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp);
  have := hb 0 (by simp); have := hb 1 (by simp); have := hb 2 (by simp); have := hb 3 (by simp); have := hb 4 (by simp)
  progress*
  all_goals try simp [*]; scalar_tac
  -- remains to show that `U128x9_as_Nat res = U64x5_as_Nat a * U64x5_as_Nat b`
  simp [*, Finset.sum_range_succ]
  ring

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
