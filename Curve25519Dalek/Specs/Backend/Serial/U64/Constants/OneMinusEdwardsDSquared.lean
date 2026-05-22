/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! Spec theorem for
`curve25519_dalek::backend::serial::u64::constants::ONE_MINUS_EDWARDS_D_SQUARED`

This constant represents `1 - d^2 (mod p)`, where `d` is the twisted Edwards curve parameter
for Curve25519 and `p = 2^255 - 19`. It is encoded as a 5-limb 51-bit `FieldElement51`.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- Spec theorem for
`curve25519_dalek::backend::serial::u64::constants::ONE_MINUS_EDWARDS_D_SQUARED`
• The function always succeeds (no panic)
• `Field51_as_Nat ONE_MINUS_EDWARDS_D_SQUARED = (1 + p - (d^2 % p)) % p`, the canonical
  reduced representation of `1 - d^2 (mod p)` (the extra `+ p` avoids underflow in Lean's
  truncated `Nat` subtraction)
• Every limb is bounded by `2 ^ 51`
-/
@[step]
theorem ONE_MINUS_EDWARDS_D_SQUARED_spec :
    ONE_MINUS_EDWARDS_D_SQUARED ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = (1 + p - (d^2 % p)) % p ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold ONE_MINUS_EDWARDS_D_SQUARED field.FieldElement51.from_limbs
  simp only [spec_ok]
  exact ⟨by decide, fun i hi => by interval_cases i <;> decide⟩

end curve25519_dalek.backend.serial.u64.constants
