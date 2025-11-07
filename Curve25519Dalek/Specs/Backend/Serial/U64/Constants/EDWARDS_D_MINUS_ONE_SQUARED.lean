/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `constants::EDWARDS_D_MINUS_ONE_SQUARED`

Specification and proof for the constant `EDWARDS_D_MINUS_ONE_SQUARED`.

This constant represents (d - 1)² (mod p) whereby d is the twisted Edwards curve parameter.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64

/-
natural language description:

    • constants.EDWARDS_D_MINUS_ONE_SQUARED is a constant representing (d - 1)² (mod p) whereby d is
      a parameter in the defining curve equation ax^2 + y^2 = 1 + dx^2y^2.
    • The field element constants.EDWARDS_D_MINUS_ONE_SQUARED is represented as five u64 limbs (51-bit limbs)

natural language specs:

    • Field51_as_Nat(constants.EDWARDS_D_MINUS_ONE_SQUARED) = (d - 1)² (mod p) where d is the mathematical representation
      of the Edwards curve parameter as a natural number.
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED`**:
- The value of constants.EDWARDS_D_MINUS_ONE_SQUARED when converted to a natural number equals
  the canonical (reduced) representation of (d - 1)² (mod p) in [0, p-1].
-/
@[progress]
theorem EDWARDS_D_MINUS_ONE_SQUARED_spec : Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED = (d - 1)^2 % p := by
  unfold constants.EDWARDS_D_MINUS_ONE_SQUARED
  decide

end curve25519_dalek.backend.serial.u64
