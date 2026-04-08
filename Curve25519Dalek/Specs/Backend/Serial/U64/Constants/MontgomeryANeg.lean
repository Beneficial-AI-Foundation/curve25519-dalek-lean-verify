/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `constants::MONTGOMERY_A_NEG`

Specification and proof for the constant `MONTGOMERY_A_NEG`.

This constant represents the negation of the Montgomery curve parameter A
in the curve equation By^2 = x^3 + Ax^2 + x. This is used internally within
the Elligator map.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::MONTGOMERY_A_NEG`**

Field51_as_Nat(constants.MONTGOMERY_A_NEG) + 486662 = p, i.e. MONTGOMERY_A_NEG represents
−486662 modulo p, the negation of the Montgomery curve parameter A. -/
@[step]
theorem MONTGOMERY_A_NEG_spec :
    MONTGOMERY_A_NEG ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result + 486662 = p ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold MONTGOMERY_A_NEG field.FieldElement51.from_limbs
  simp only [spec_ok]
  decide

end curve25519_dalek.backend.serial.u64.constants
