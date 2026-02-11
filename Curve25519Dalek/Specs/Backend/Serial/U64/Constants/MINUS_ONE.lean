/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `constants::MINUS_ONE`

Specification and proof for the constant `MINUS_ONE`.

This constant represents −1 modulo p as a field element in the 51-bit limb
representation (five u64 limbs).

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.MINUS_ONE is the canonical field element representing −1 (mod p)
    • In canonical [0, p-1] representation, −1 (mod p) equals p − 1
    • The field element constants.MINUS_ONE is represented as five u64 limbs (51-bit limbs)

natural language specs:

    • Field51_as_Nat(constants.MINUS_ONE) = p − 1
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.MINUS_ONE`**:
- The value of constants.MINUS_ONE, when converted to a natural number, equals p − 1
  (the canonical representative of −1 modulo p in [0, p-1]).
-/
@[progress]
theorem MINUS_ONE_spec : Field51_as_Nat MINUS_ONE = p - 1 := by
  unfold MINUS_ONE
  decide

end curve25519_dalek.backend.serial.u64.constants
