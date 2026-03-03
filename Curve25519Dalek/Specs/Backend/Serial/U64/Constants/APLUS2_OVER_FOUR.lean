/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux

/-! # Spec Theorem for `constants::APLUS2_OVER_FOUR`

Specification and proof for the constant `APLUS2_OVER_FOUR`.

This constant represents (A+2)/4 where A is the Montgomery curve parameter.
For Curve25519, A = 486662, so APLUS2_OVER_FOUR = 121666.

This constant is used in the Montgomery ladder differential addition formula.

**Source**: curve25519-dalek/src/backend/serial/u64/constants.rs:108-109
-/

open Aeneas Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.APLUS2_OVER_FOUR is a constant representing (A+2)/4
      where A is the Montgomery curve parameter
    • The field element constants.APLUS2_OVER_FOUR is represented as five u64 limbs (51-bit limbs)
    • The value is 121666 = (486662 + 2) / 4

natural language specs:

    • Field51_as_Nat(constants.APLUS2_OVER_FOUR) = 121666
-/

/-- **Spec for `backend.serial.u64.constants.APLUS2_OVER_FOUR`**:
- The value of constants.APLUS2_OVER_FOUR when converted to a natural number equals 121666
-/
@[simp]
theorem APLUS2_OVER_FOUR_spec : Field51_as_Nat APLUS2_OVER_FOUR = 121666 := by
  unfold APLUS2_OVER_FOUR
  decide

/-- **Bounds lemma for `APLUS2_OVER_FOUR`**:

All limbs of APLUS2_OVER_FOUR are bounded by 2^54, which is used in the Montgomery
differential addition formula (`Montgomery.ProjectivePoint.DifferentialAddAndDouble`).

This helper lemma provides bounds guarantees without unfolding the constant definition.
-/

theorem APLUS2_OVER_FOUR_bound :
    ∀ i < 5, APLUS2_OVER_FOUR[i]!.val < 2 ^ 54 := by
  intro i _
  unfold APLUS2_OVER_FOUR
  interval_cases i <;> decide

end curve25519_dalek.backend.serial.u64.constants
