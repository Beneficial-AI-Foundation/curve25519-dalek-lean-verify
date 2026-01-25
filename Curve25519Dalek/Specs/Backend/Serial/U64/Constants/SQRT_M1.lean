/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `constants::SQRT_M1`

Specification and proof for the constant `SQRT_M1`.

This constant represents one of the square roots of -1 modulo p.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.SQRT_M1 is a constant representing one of the square roots of -1 modulo p.
    • The field element constants.SQRT_M1 is represented as five u64 limbs (51-bit limbs)

natural language specs:

    • Field51_as_Nat(constants.SQRT_M1) ≡ sqrt(-1) (mod p), which is equivalent to
      Field51_as_Nat(constants.SQRT_M1)^2 ≡ p - 1 (mod p).
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.SQRT_M1`**:
- Field51_as_Nat(constants.SQRT_M1) ≡ sqrt(-1) (mod p), which is equivalent to
  Field51_as_Nat(constants.SQRT_M1)^2 ≡ p - 1 (mod p).
-/
@[progress]
theorem SQRT_M1_spec :
    ok SQRT_M1 ⦃ _ => (Field51_as_Nat SQRT_M1)^2 % p = p - 1 ⦄ := by
  have h : (Field51_as_Nat SQRT_M1)^2 % p = p - 1 := by
    unfold SQRT_M1
    decide
  simpa using h

end curve25519_dalek.backend.serial.u64.constants
