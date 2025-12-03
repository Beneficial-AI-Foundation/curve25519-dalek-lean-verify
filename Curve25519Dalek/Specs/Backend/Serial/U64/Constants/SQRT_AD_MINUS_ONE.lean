/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `constants::SQRT_AD_MINUS_ONE`

Specification and proof for the constant `SQRT_AD_MINUS_ONE`.

This constant represents sqrt(a*d - 1) where a and d are the twisted Edwards
curve parameters in the defining equation ax^2 + y^2 = 1 + dx^2y^2, with a = -1 (mod p).

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64

/-
natural language description:

    • constants.SQRT_AD_MINUS_ONE is a constant representing one of the square roots of (a*d - 1) (mod p)
      where a and d are the parameters in the defining curve equation ax^2 + y^2 = 1 + dx^2y^2
      (for Curve25519 we have a = -1).
    • The field element constants.SQRT_AD_MINUS_ONE is represented as five u64 limbs (51-bit limbs)

natural language specs:

    • Field51_as_Nat(constants.SQRT_AD_MINUS_ONE)^2 ≡ (a*d - 1) (mod p).
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.SQRT_AD_MINUS_ONE`**:
- Field51_as_Nat(constants.SQRT_AD_MINUS_ONE) is a square root of (a*d - 1) modulo p, i.e.
  `(Field51_as_Nat constants.SQRT_AD_MINUS_ONE)^2 ≡ (a*d - 1) (mod p)`.
-/
@[progress]
theorem SQRT_AD_MINUS_ONE_spec :
    (Field51_as_Nat constants.SQRT_AD_MINUS_ONE)^2 % p = (a * d - 1) % p := by
  unfold constants.SQRT_AD_MINUS_ONE
  decide

end curve25519_dalek.backend.serial.u64
