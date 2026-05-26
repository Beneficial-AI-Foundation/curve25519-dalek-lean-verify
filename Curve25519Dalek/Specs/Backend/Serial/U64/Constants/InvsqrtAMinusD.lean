/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::INVSQRT_A_MINUS_D`

This constant represents `1 / sqrt(a - d) (mod p)`, where `a` and `d` are the twisted Edwards
curve parameters appearing in the defining equation `a*x^2 + y^2 = 1 + d*x^2*y^2` and
`p = 2^255 - 19`. It is encoded as a 5-limb 51-bit `FieldElement51`.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::INVSQRT_A_MINUS_D`**
• The function always succeeds (no panic)
• `(Field51_as_Nat INVSQRT_A_MINUS_D)^2 * (a - d) ≡ 1 (mod p)`, i.e. it inverts `sqrt(a - d)`
• Every limb is bounded by `2 ^ 51`
-/
@[step]
theorem INVSQRT_A_MINUS_D_spec :
    INVSQRT_A_MINUS_D ⦃ (result : field.FieldElement51) =>
      (Field51_as_Nat result)^2 * (a - d) % p = 1 ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold INVSQRT_A_MINUS_D field.FieldElement51.from_limbs
  simp only [spec_ok]
  decide

end curve25519_dalek.backend.serial.u64.constants
