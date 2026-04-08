/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `constants::ONE_MINUS_EDWARDS_D_SQUARED`

Specification and proof for the constant `ONE_MINUS_EDWARDS_D_SQUARED`.

This constant represents 1 - d² (mod p) whereby d is the twisted Edwards curve parameter.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u64::constants::ONE_MINUS_EDWARDS_D_SQUARED`**
- The value of constants.ONE_MINUS_EDWARDS_D_SQUARED when converted to a natural number equals
  the canonical (reduced) representation of (1 - d²) (mod p) in [0, p-1].
  Note: the extra " + p" in the spec theorem is to avoided hitting 0 in the truncated subtraction
  implemented by Lean. -/
@[step]
theorem ONE_MINUS_EDWARDS_D_SQUARED_spec :
    ONE_MINUS_EDWARDS_D_SQUARED ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = (1 + p - (d^2 % p)) % p ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold ONE_MINUS_EDWARDS_D_SQUARED field.FieldElement51.from_limbs
  simp only [spec_ok]
  exact ⟨by decide, fun i hi => by interval_cases i <;> decide⟩

end curve25519_dalek.backend.serial.u64.constants
