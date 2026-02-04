/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `constants::MONTGOMERY_A`

Specification and proof for the constant `MONTGOMERY_A`.

This constant represents the Montgomery curve parameter A in the curve equation
By^2 = x^3 + Ax^2 + x.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.MONTGOMERY_A is a constant representing the Montgomery curve parameter A
      in the defining curve equation By^2 = x^3 + Ax^2 + x.
    • The field element constants.MONTGOMERY_A is represented as five u64 limbs (51-bit limbs)
    • The value is 486662

natural language specs:

    • Field51_as_Nat(constants.MONTGOMERY_A) = 486662 where 486662 is the mathematical
      representation of the Montgomery curve parameter A as a natural number.
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.MONTGOMERY_A`**:
- The value of constants.MONTGOMERY_A when converted to a natural number equals 486662
-/
@[progress]
theorem MONTGOMERY_A_spec : Field51_as_Nat MONTGOMERY_A = 486662 := by
  unfold MONTGOMERY_A
  decide

end curve25519_dalek.backend.serial.u64.constants
