/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::negate`

This function computes the additive inverse (negation) of a `FieldElement51` in 𝔽_p
(p = 2^255 - 19).

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::negate`**
• The function always succeeds (no panic) provided every input limb is `< 2 ^ 54`
• `Field51_as_Nat self + Field51_as_Nat neg ≡ 0 (mod p)`, i.e. `neg` is the additive inverse
• Every output limb is `< 2 ^ 52`
-/
@[step]
theorem negate_spec (self : FieldElement51) (h : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    negate self ⦃ (neg : FieldElement51) =>
      Field51_as_Nat self + Field51_as_Nat neg ≡ 0 [MOD p] ∧
      ∀ i < 5, neg[i]!.val < 2 ^ 52 ⦄ := by
  unfold negate
  step*
  constructor
  · have : 16 * p =
      36028797018963664 * 2 ^ 0 +
      36028797018963952 * 2 ^ 51 +
      36028797018963952 * 2 ^ 102 +
      36028797018963952 * 2 ^ 153 +
      36028797018963952 * 2 ^ 204 := by simp [p]
    simp_all [Nat.ModEq, Field51_as_Nat, Finset.sum_range_succ, Array.make]
    grind
  · assumption

end curve25519_dalek.backend.serial.u64.field.FieldElement51
