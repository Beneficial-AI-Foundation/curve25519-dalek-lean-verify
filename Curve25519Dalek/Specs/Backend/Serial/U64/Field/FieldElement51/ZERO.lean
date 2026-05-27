/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromLimbs

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::ZERO`

This constant represents the additive identity element `0` in 𝔽_p (p = 2^255 - 19). It is
stored as the five-limb array `[0, 0, 0, 0, 0]`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::ZERO`**
• The function always succeeds (no panic)
• `Field51_as_Nat ZERO = 0`, the additive identity of 𝔽_p
• Every limb is bounded by `2 ^ 51`
-/
@[step]
theorem ZERO_spec : ZERO ⦃ (result : FieldElement51) =>
    Field51_as_Nat result = 0 ∧
    (∀ i< 5, (result[i]!.val) < 2^51 )⦄ := by
  unfold ZERO
  step*
  simp only [*]
  decide

end curve25519_dalek.backend.serial.u64.field.FieldElement51
