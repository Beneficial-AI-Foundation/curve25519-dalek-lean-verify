/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::MINUS_ONE`

This constant represents `-1 (mod p)` as a `FieldElement51`, encoded as five 51-bit u64
limbs.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::MINUS_ONE`**
• The function always succeeds (no panic)
• `Field51_as_Nat MINUS_ONE = p - 1`, the canonical representative of `-1 (mod p)`
• Every limb is bounded by `2 ^ 51`
-/
@[step]
theorem MINUS_ONE_spec :
    MINUS_ONE ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = p - 1 ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold MINUS_ONE field.FieldElement51.from_limbs
  simp only [spec_ok]
  exact ⟨by decide, fun i hi => by interval_cases i <;> decide⟩

end curve25519_dalek.backend.serial.u64.constants
