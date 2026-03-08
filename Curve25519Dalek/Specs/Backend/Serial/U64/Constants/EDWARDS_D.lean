/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `constants::EDWARDS_D`

Specification and proof for the constant `EDWARDS_D`.

This constant represents the twisted Edwards curve parameter d.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.EDWARDS_D is a constant representing the Edwards curve parameter d
      in the defining curve equation ax^2 + y^2 = 1 + dx^2y^2.
    • The field element constants.EDWARDS_D is represented as five u64 limbs (51-bit limbs)

natural language specs:

    • Field51_as_Nat(constants.EDWARDS_D) = d where d is the mathematical representation
      of the Edwards curve parameter as a natural number.
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.EDWARDS_D`**:
- The value of constants.EDWARDS_D when converted to a natural number equals d
-/
@[progress]
theorem EDWARDS_D_spec : EDWARDS_D ⦃ result => Field51_as_Nat result = d ⦄ := by
  unfold EDWARDS_D field.FieldElement51.from_limbs
  simp only [spec_ok]
  decide

end curve25519_dalek.backend.serial.u64.constants
