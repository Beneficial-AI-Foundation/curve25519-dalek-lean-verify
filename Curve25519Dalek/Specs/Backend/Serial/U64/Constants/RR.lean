/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

set_option exponentiation.threshold 260

/-! # Spec Theorem for `constants::RR`

Specification and proof for the constant `RR`.

This constant represents R² mod L, where R = 2^260 is the Montgomery constant
and L is the group order. It is used in Montgomery form conversions.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64

/-
natural language description:

    • RR is a constant representing R² mod L where R = 2^260 and L is the group order
    • The scalar is represented as five u64 limbs (52-bit limbs)

natural language specs:

    • Scalar52_as_Nat(RR) ≡ R² (mod L) where R = 2^260
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.RR`**:
- The value of RR when converted to a natural number is congruent to R² modulo L
-/
theorem RR_spec : Scalar52_as_Nat constants.RR ≡ R ^ 2 [MOD L] := by
  unfold constants.RR
  decide

end curve25519_dalek.backend.serial.u64
