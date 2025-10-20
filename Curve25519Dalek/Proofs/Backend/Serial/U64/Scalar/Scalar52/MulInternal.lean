import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Aux
import Curve25519Dalek.Proofs.Defs
import Curve25519Dalek.Proofs.Backend.Serial.U64.Scalar.M

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 3000000

/-! # MulInternal

The main statement concerning `mul_internal` is `mul_internal_spec` (below).
-/

open Aeneas.Std Result
open curve25519_dalek
open backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
-- This activates/deactives some simps to reason about lists
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

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
    unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try {
      subst_vars
      have := ha 0 (by omega)
      have := ha 1 (by omega)
      have := ha 2 (by omega)
      have := ha 3 (by omega)
      have := ha 4 (by omega)
      have := hb 0 (by omega)
      have := hb 1 (by omega)
      have := hb 2 (by omega)
      have := hb 3 (by omega)
      have := hb 4 (by omega)
      scalar_tac
    }
    -- remains to show that `U128x9_as_Nat res = U64x5_as_Nat a * U64x5_as_Nat b`
    simp [U128x9_as_Nat, U64x5_as_Nat, Finset.sum_range_succ, *]
    ring



end curve25519_dalek.backend.serial.u64.scalar.Scalar52
