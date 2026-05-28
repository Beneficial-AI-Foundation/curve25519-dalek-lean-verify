/-
Copyright (c) 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::square`

This function computes the square of a `FieldElement51` in 𝔽_p (p = 2^255 - 19).

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::square`**
• The function always succeeds (no panic) provided every input limb is `< 2 ^ 54`
• `Field51_as_Nat result ≡ (Field51_as_Nat a)^2 (mod p)`
• Every output limb is `< 2 ^ 52`
-/
@[step]
theorem square_spec (a : Array U64 5#usize) (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    square a ⦃ (r : FieldElement51) =>
      Field51_as_Nat r ≡ (Field51_as_Nat a)^2 [MOD p] ∧
      (∀ i < 5, r[i]!.val < 2 ^ 52) ⦄ := by
  unfold square
  step*

end curve25519_dalek.backend.serial.u64.field.FieldElement51
