/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D2`

This constant represents `2 * d (mod p)`, where `d` is the twisted Edwards curve parameter
for Curve25519 and `p = 2^255 - 19`. It is encoded as a 5-limb 52-bit `FieldElement51`.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D2`**
• The function always succeeds (no panic)
• `Field51_as_Nat EDWARDS_D2 = (2 * d) % p`, the canonical reduced representation
• Every limb is bounded by `2 ^ 52`
-/
@[step]
theorem EDWARDS_D2_spec :
    EDWARDS_D2 ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = (2 * d) % p ∧
      ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by
  unfold EDWARDS_D2 field.FieldElement51.from_limbs
  simp only [spec_ok]
  decide

end curve25519_dalek.backend.serial.u64.constants
