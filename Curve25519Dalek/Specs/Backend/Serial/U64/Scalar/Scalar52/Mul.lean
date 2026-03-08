/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinxing Lim
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR

/-! # Spec Theorem for `Scalar52::mul`

Specification and proof for `Scalar52::mul`.

This function performs regular scalar multiplication (not Montgomery multiplication).

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262
set_option linter.style.emptyLine false
/-
natural language description:

    • Takes two input scalars a and b (not in Montgomery form) and returns
      a scalar representing their product modulo L.

    • The implementation works by:
      1. Computing mul_internal(a, b) to get the polynomial product
      2. Applying montgomery_reduce to get ab * R^(-1) (in Montgomery form)
      3. Multiplying by RR (which is R^2 mod L) via mul_internal
      4. Applying montgomery_reduce again to convert back to normal form

    • The double Montgomery reduction with RR effectively computes:
      ((a * b * R^(-1)) * R^2 * R^(-1)) = a * b (mod L)

natural language specs:

    • For any two scalars a and b:
      - The function returns successfully
      - Scalar52_as_Nat(result) ≡ Scalar52_as_Nat(a) * Scalar52_as_Nat(b) (mod L)
      - Each limb of the result is bounded by 2^52
-/

/- Helper lemmas/theorems -/

-- Helper theorem to cancel R [mod L] on right retrieved from Curve25519Dalek.Specs.Scalar.Scalar.Reduce.lean
-- NOTE: We should refactoring such helper theorems into a common file to avoid duplication
theorem cancelR {a b : ℕ} (h : a * R ≡ b * R [MOD L]) : a ≡ b [MOD L] := by
  have hcoprime : Nat.Coprime R L := by
    unfold R L Nat.Coprime
    simp
  have h1 := Nat.Coprime.symm hcoprime
  exact Nat.ModEq.cancel_right_of_coprime h1 h

/- End of helper lemmas/theorems -/

/-- **Spec and proof concerning `scalar.Scalar52.mul`**:
- No panic (always returns successfully)
- The result represents the product of the two input scalars modulo L
- Input scalars should have limbs bounded by 2^62 (standard Scalar52 representation)
- Output limbs are bounded by 2^52
-/
@[progress]
theorem mul_spec (a b : Scalar52)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62) :
    mul a b ⦃ ( result : Scalar52 ) =>
      Scalar52_as_Nat result ≡ Scalar52_as_Nat a * Scalar52_as_Nat b [MOD L] ∧
      ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by
  unfold mul
  progress*
  -- -- 2. To prove ∀ i < 5, ↑constants.RR[i]! < 2 ^ 62
  · unfold constants.RR; decide
  refine ⟨?_, by grind⟩
  -- 3a. To prove Scalar52_as_Nat res ≡ Scalar52_as_Nat a * Scalar52_as_Nat b [MOD L]
  -- i. res * R ≡ ab * RR [MOD L]
  have h_res_R_ab_RR : Scalar52_as_Nat result * R ≡ Scalar52_as_Nat ab * Scalar52_as_Nat constants.RR [MOD L] := by
    rw [a2_post1] at result_post1
    rw [Nat.ModEq]
    exact result_post1
  -- ii. res * R ≡ ab * R * R [MOD L]
  have h_res_R_ab_R_R : Scalar52_as_Nat result * R ≡ Scalar52_as_Nat ab * R * R [MOD L] := by
    have := curve25519_dalek.backend.serial.u64.constants.RR_spec
    grind [Nat.ModEq, Nat.mul_mod, Nat.pow_two, Nat.mul_assoc]
  -- iii. res * R ≡ a1 * R [MOD L]
  have h_res_R_a1_R : Scalar52_as_Nat result * R ≡ Scalar52_wide_as_Nat a1 * R  [MOD L] := by
    rw [← Nat.ModEq] at ab_post1
    have h_temp : Scalar52_as_Nat ab * R * R ≡ Scalar52_wide_as_Nat a1 * R [MOD L] := by
      exact Nat.ModEq.mul_right R ab_post1
    exact Nat.ModEq.trans h_res_R_ab_R_R h_temp
  -- iv. res * R ≡ a * b * R [MOD L]
  have h_res_R_a_b_R : Scalar52_as_Nat result * R ≡ Scalar52_as_Nat a * Scalar52_as_Nat b * R  [MOD L] := by
    rw [a1_post1] at h_res_R_a1_R
    exact h_res_R_a1_R
  -- v. res ≡ a * b [MOD L]
  grind [cancelR]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
