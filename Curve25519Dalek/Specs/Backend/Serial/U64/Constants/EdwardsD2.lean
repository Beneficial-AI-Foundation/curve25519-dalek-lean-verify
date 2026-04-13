/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `constants::EDWARDS_D2`

Specification and proof for the constant `EDWARDS_D2`.

This constant represents 2*d (mod p) whereby d is the twisted Edwards curve parameter.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D2`**

The value of `EDWARDS_D2` when converted to a natural number equals
the canonical (reduced) representation of 2*d (mod p) in [0, p-1]. -/
@[step]
theorem EDWARDS_D2_spec :
    EDWARDS_D2 ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = (2 * d) % p ∧
      ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by
  unfold EDWARDS_D2 field.FieldElement51.from_limbs
  simp only [spec_ok]
  decide

end curve25519_dalek.backend.serial.u64.constants
