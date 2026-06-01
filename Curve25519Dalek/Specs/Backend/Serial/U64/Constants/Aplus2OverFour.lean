/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromLimbs

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::APLUS2_OVER_FOUR`

This constant represents (A+2)/4 where A is the Montgomery curve parameter.
For Curve25519, A = 486662, so APLUS2_OVER_FOUR = 121666.
This constant is used in the Montgomery ladder differential addition formula.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs:108-109"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::APLUS2_OVER_FOUR`**
• The function always succeeds (no panic)
• The value of `APLUS2_OVER_FOUR` when converted to a natural number equals 121666
• Every limb is bounded by `2 ^ 54`, which is used in the Montgomery differential addition formula.
-/
@[step]
theorem APLUS2_OVER_FOUR_spec :
    APLUS2_OVER_FOUR ⦃ (result : FieldElement51) =>
      Field51_as_Nat result = 121666 ∧
      ∀ i < 5, result[i]!.val < 2 ^ 54 ⦄ := by
  unfold APLUS2_OVER_FOUR
  step*
  constructor
  · simp only [*]; decide
  · simp only [*]; intro i hi; interval_cases i <;> decide

end curve25519_dalek.backend.serial.u64.constants
