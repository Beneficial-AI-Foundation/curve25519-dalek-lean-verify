/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `constants::INVSQRT_A_MINUS_D`

Specification and proof for the constant `INVSQRT_A_MINUS_D`.

This constant represents 1/sqrt(a-d) where a and d are the twisted Edwards curve parameters
in the defining equation ax^2 + y^2 = 1 + dx^2y^2.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64

/-
natural language description:

    • constants.INVSQRT_A_MINUS_D is a constant representing 1/sqrt(a-d) where a and d
      are the parameters in the defining curve equation ax^2 + y^2 = 1 + dx^2y^2.
    • The field element constants.INVSQRT_A_MINUS_D is represented as five u64 limbs (51-bit limbs)

natural language specs:

    • Field51_as_Nat(constants.INVSQRT_A_MINUS_D)^2 * (a - d) ≡ 1 (mod p) where a and d
      are the mathematical representations of the Edwards curve parameters as integers.
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.INVSQRT_A_MINUS_D`**:
- Field51_as_Nat(constants.INVSQRT_A_MINUS_D)^2 * (a - d) ≡ 1 (mod p), which is equivalent
  to Field51_as_Nat(constants.INVSQRT_A_MINUS_D) ≡ 1/sqrt(a-d) (mod p).
-/
theorem INVSQRT_A_MINUS_D_spec :
    (Field51_as_Nat constants.INVSQRT_A_MINUS_D)^2 * (a - d) % p = 1 := by
  unfold constants.INVSQRT_A_MINUS_D
  decide

end curve25519_dalek.backend.serial.u64
