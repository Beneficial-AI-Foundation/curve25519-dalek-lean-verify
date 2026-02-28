/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `constants::ONE_MINUS_EDWARDS_D_SQUARED`

Specification and proof for the constant `ONE_MINUS_EDWARDS_D_SQUARED`.

This constant represents 1 - d² (mod p) whereby d is the twisted Edwards curve parameter.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.ONE_MINUS_EDWARDS_D_SQUARED is a constant representing 1 - d² (mod p) whereby d is a parameter
      in the defining curve equation ax^2 + y^2 = 1 + dx^2y^2.
    • The field element constants.ONE_MINUS_EDWARDS_D_SQUARED is represented as five u64 limbs (51-bit limbs)
    • Note that the original Rust comment states
      "One minus edwards `d` value squared, equal to `(1 - (-121665/121666) mod p) pow 2`",
      however, there seems to be a typo/error in this comment, as it appears that the constant (as defined) is
      congruent to 1 - d^2 and not to (1 - d)^2.

natural language specs:

    • Field51_as_Nat(constants.ONE_MINUS_EDWARDS_D_SQUARED) = (1 - d²) (mod p) where d is the mathematical representation
      of the Edwards curve parameter as a natural number.
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED`**:
- The value of constants.ONE_MINUS_EDWARDS_D_SQUARED when converted to a natural number equals
  the canonical (reduced) representation of (1 - d²) (mod p) in [0, p-1].
  Note: the extra " + p" in the spec theorem is to avoided hitting 0 in the truncated subtraction
  implemented by Lean.
-/
@[progress]
theorem ONE_MINUS_EDWARDS_D_SQUARED_spec :
    ONE_MINUS_EDWARDS_D_SQUARED ⦃ result =>
      Field51_as_Nat result = (1 + p - (d^2 % p)) % p ⦄ := by
  unfold ONE_MINUS_EDWARDS_D_SQUARED field.FieldElement51.from_limbs
  simp only [spec_ok]
  decide

end curve25519_dalek.backend.serial.u64.constants
