/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Std.Do
import Curve25519Dalek.mvcgen
open Std.Do

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
@[spec]
theorem mul_internal_hoare_spec (a b : Array U64 5#usize)
(ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62)
(hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 62) :
⦃⌜True⌝⦄
mul_internal a b
⦃⇓ result => ⌜Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat b⌝⦄
  := by
  mvcgen
  rcases mul_internal_spec a b ha hb with ⟨result, hres, hmul, _hbounds⟩
  simp [Std.Do.wp, PostCond.noThrow, hres, hmul]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
