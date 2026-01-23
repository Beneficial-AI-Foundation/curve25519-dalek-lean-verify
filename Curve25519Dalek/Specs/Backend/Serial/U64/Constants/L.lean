/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `constants::L`

Specification and proof for the constant `L`.

This constant represents the group order L of Curve25519.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.L is a constant representing the group order L of Curve25519
    • The scalar constants.L is represented as five u64 limbs (52-bit limbs)

natural language specs:

    • Scalar52_as_Nat(constants.L) = L where L is the group order
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.L`**:
- The value of constants.L when converted to a natural number equals L
-/
@[progress]
theorem L_spec : ok L ⦃ _ => Scalar52_as_Nat L = _root_.L ⦄ := by
  have h : Scalar52_as_Nat L = _root_.L := by
    unfold L
    decide
  simpa using h

end curve25519_dalek.backend.serial.u64.constants
