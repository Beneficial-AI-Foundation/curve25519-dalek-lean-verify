/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce

/-! # Spec Theorem for `FieldElement51::negate`

Specification and proof for `FieldElement51::negate`.

Computes the additive inverse (negation) of a field element in 𝔽_p where p = 2^255 - 19.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
Natural language description:

    • Computes the additive inverse of a field element in 𝔽_p where p = 2^255 - 19
    • The field element is represented in radix 2^51 form with five u64 limbs
    • The implementation subtracts each input limb from appropriately chosen constants (= 16*p)
      to avoid underflow and then (weakly) reduces the result modulo p
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.negate`**:
- The result `neg` represents the additive inverse of the input `self` in 𝔽_p.
- All the limbs of the result are ≤ 2^(51 + ε).
- Requires that input limbs of `self` are bounded to avoid underflow. -/
@[progress]
theorem negate_spec (self : FieldElement51) (h : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    negate self ⦃ (neg : FieldElement51) =>
      Field51_as_Nat self + Field51_as_Nat neg ≡ 0 [MOD p] ∧
      ∀ i < 5, neg[i]!.val < 2 ^ 52 ⦄ := by
  unfold negate
  progress*
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
