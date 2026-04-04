/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `constants::EDWARDS_D_MINUS_ONE_SQUARED`

Specification and proof for the constant `EDWARDS_D_MINUS_ONE_SQUARED`.

This constant represents (d - 1)² (mod p) whereby d is the twisted Edwards curve parameter.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- Spec theorem for `backend::serial::u64::constants::EDWARDS_D_MINUS_ONE_SQUARED`

The value of `EDWARDS_D_MINUS_ONE_SQUARED` when converted to a natural number equals
the canonical (reduced) representation of (d - 1)² (mod p) in [0, p-1]. -/
@[step]
theorem EDWARDS_D_MINUS_ONE_SQUARED_spec :
    EDWARDS_D_MINUS_ONE_SQUARED ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = (d - 1) ^ 2 % p ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold EDWARDS_D_MINUS_ONE_SQUARED field.FieldElement51.from_limbs
  simp only [spec_ok]
  exact ⟨by decide, fun i hi => by interval_cases i <;> decide⟩

end curve25519_dalek.backend.serial.u64.constants
