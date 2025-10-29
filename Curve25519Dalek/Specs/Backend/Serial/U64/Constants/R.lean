/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

set_option exponentiation.threshold 260

/-! # Spec Theorem for `constants::R`

Specification and proof for the constant `R`.

This constant represents R mod L, where R = 2^260 is the Montgomery constant
and L is the group order. It is used in Montgomery form conversions.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64

/-
natural language description:

    • constants.R is a constant representing R mod L where R = 2^260 and L is the group order
    • The scalar constants.R is represented as five u64 limbs (52-bit limbs)

natural language specs:

    • Scalar52_as_Nat(constants.R) ≡ R (mod L) where R = 2^260
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.R`**:
- The value of constants.R when converted to a natural number is congruent to R modulo L
-/
theorem R_spec : Scalar52_as_Nat constants.R ≡ R [MOD L] := by
  unfold constants.R
  decide

end curve25519_dalek.backend.serial.u64
