/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `constants::EDWARDS_D`

Specification and proof for the constant `EDWARDS_D`.

This constant represents the twisted Edwards curve parameter d.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D`**

Field51_as_Nat(constants.EDWARDS_D) = d where d is the mathematical representation of the Edwards
curve parameter as a natural number. -/
@[step]
theorem EDWARDS_D_spec :
    EDWARDS_D ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = d ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold EDWARDS_D field.FieldElement51.from_limbs
  simp only [spec_ok]
  exact ⟨by decide, fun i hi => by interval_cases i <;> decide⟩

end curve25519_dalek.backend.serial.u64.constants
