/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `constants::EDWARDS_D2`

Specification and proof for the constant `EDWARDS_D2`.

This constant represents 2*d (mod p) whereby d is the twisted Edwards curve parameter.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.EDWARDS_D2 is a constant representing 2*d (mod p) whereby d is a
      parameter in the defining curve equation ax^2 + y^2 = 1 + dx^2y^2.
    • The field element constants.EDWARDS_D2 is represented as five u64 limbs (51-bit limbs)

natural language specs:

    • Field51_as_Nat(constants.EDWARDS_D2) = 2*d (mod p) where d is the mathematical representation
      of the Edwards curve parameter as a natural number.
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.EDWARDS_D2`**:
- The value of constants.EDWARDS_D2 when converted to a natural number equals
  the canonical (reduced) representation of 2*d (mod p) in [0, p-1].
-/
@[progress]
theorem EDWARDS_D2_spec : ok EDWARDS_D2 ⦃ _ => Field51_as_Nat EDWARDS_D2 = (2 * d) % p ⦄ := by
  have h : Field51_as_Nat EDWARDS_D2 = (2 * d) % p := by
    unfold EDWARDS_D2
    decide
  simpa using h

end curve25519_dalek.backend.serial.u64.constants
