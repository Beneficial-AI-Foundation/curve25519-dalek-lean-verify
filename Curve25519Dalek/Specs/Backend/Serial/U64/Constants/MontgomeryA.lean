/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::MONTGOMERY_A`

This constant represents the Montgomery curve parameter `A` in the curve equation
`B*y^2 = x^3 + A*x^2 + x` for Curve25519, where `A = 486662`.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::MONTGOMERY_A`**
• The function always succeeds (no panic)
• `Field51_as_Nat MONTGOMERY_A = 486662`
• Every limb is bounded by `2 ^ 51`
-/
@[step]
theorem MONTGOMERY_A_spec :
    MONTGOMERY_A ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = 486662 ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold MONTGOMERY_A field.FieldElement51.from_limbs
  simp only [spec_ok]
  decide

end curve25519_dalek.backend.serial.u64.constants
