/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-!
# Spec theorem

Specification for
`curve25519_dalek::backend::serial::u64::constants::EDWARDS_D_MINUS_ONE_SQUARED`.

This constant represents `(d - 1)^2 (mod p)`, where `d` is the twisted Edwards curve
parameter for Curve25519 and `p = 2^255 - 19`. It is encoded as a 5-limb 51-bit
`FieldElement51`.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem**

Specification for
`curve25519_dalek::backend::serial::u64::constants::EDWARDS_D_MINUS_ONE_SQUARED`.

• The function always succeeds (no panic)
• `Field51_as_Nat EDWARDS_D_MINUS_ONE_SQUARED = (d - 1)^2 % p` (canonical reduced form)
• Every limb is bounded by `2 ^ 51`
-/
@[step]
theorem EDWARDS_D_MINUS_ONE_SQUARED_spec :
    EDWARDS_D_MINUS_ONE_SQUARED ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = (d - 1) ^ 2 % p ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold EDWARDS_D_MINUS_ONE_SQUARED field.FieldElement51.from_limbs
  simp only [spec_ok]
  exact ⟨by decide, fun i hi => by interval_cases i <;> decide⟩

end curve25519_dalek.backend.serial.u64.constants
