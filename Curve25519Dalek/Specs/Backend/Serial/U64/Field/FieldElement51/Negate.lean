/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce

/-! # Spec Theorem for `FieldElement51::negate`

Specification and proof for `FieldElement51::negate`.

This function computes the additive inverse (negation) of a field element in 𝔽_p where p = 2^255 - 19.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
Natural language description:

    • Computes the additive inverse of a field element in 𝔽_p where p = 2^255 - 19
    • The field element is represented in radix 2^51 form with five u64 limbs
    • The implementation subtracts each input limb from appropriately chosen constants (= 16*p)
      to avoid underflow and then (weakly) reduces the result modulo p

Natural language specs:

    • The function always succeeds (no panic)
    • For an appropriately bounded field element r, the result r_inv satisfies:
      (Field51_as_Nat(r) + Field51_as_Nat(r_inv)) ≡ 0 (mod p)
-/

/- TODO impl OfNat and OfScientific for `FieldElement51` -/

@[progress]
theorem negate_spec (r : FieldElement51) (h : ∀ i < 5, r[i]!.val < 2 ^ 54) :
    ∃ r_inv, negate r = ok r_inv ∧
    (Field51_as_Nat r + Field51_as_Nat r_inv) % p = 0 ∧
    (∀ i < 5, r_inv[i]!.val ≤ 2^51 + (2^13 - 1) * 19) := by
  unfold negate
  progress*
  · -- BEGIN TASK
    have := h 0 (by simp); simp_all; grind
    -- END TASK
  · -- BEGIN TASK
    have := h 1 (by simp); simp_all; grind
    -- END TASK
  · -- BEGIN TASK
    have := h 2 (by simp); simp_all; grind
    -- END TASK
  · -- BEGIN TASK
    have := h 3 (by simp); simp_all; grind
    -- END TASK
  · -- BEGIN TASK
    have := h 4 (by simp); simp_all; grind
    -- END TASK
  constructor
  · -- BEGIN TASK
    have : 16 * p =
      36028797018963664 * 2^0 +
      36028797018963952 * 2^51 +
      36028797018963952 * 2^102 +
      36028797018963952 * 2^153 +
      36028797018963952 * 2^204 := by simp [p]
    simp_all [Nat.ModEq, Field51_as_Nat, Finset.sum_range_succ, Array.make, Array.getElem!_Nat_eq]
    grind
    -- END TASK
  · -- BEGIN TASK
    assumption
    -- END TASK

end curve25519_dalek.backend.serial.u64.field.FieldElement51
