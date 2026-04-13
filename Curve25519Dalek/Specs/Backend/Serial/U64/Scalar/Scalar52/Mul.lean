/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinxing Lim
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.Rr

/-! # Spec Theorem for `Scalar52::mul`

This function performs regular scalar multiplication (not Montgomery multiplication).

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262

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

/-- **Spec theorem for `scalar.Scalar52.mul`**:
- The result represents the product of the two input scalars modulo L
- Input scalars should have limbs bounded by 2^62 (standard Scalar52 representation)
- Output limbs are bounded by 2^52
- `h_value`: The first `montgomery_reduce` needs `a*b < R*L` to guarantee the intermediate
  result is < 2*L (see `MontgomeryReduce.lean` docstring). The second reduce is auto-satisfied
  since its input is `ab * RR` where `ab < L` and `RR < L`, so `ab*RR < L² < R*L`. -/
@[step]
theorem mul_spec (a b : Scalar52)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62)
    (h_value : Scalar52_as_Nat a * Scalar52_as_Nat b < R * L) :
    mul a b ⦃ ( result : Scalar52 ) =>
      Scalar52_as_Nat result ≡ Scalar52_as_Nat a * Scalar52_as_Nat b [MOD L] ∧
      Scalar52_as_Nat result < L ∧ ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by
  unfold mul
  let* ⟨ a1, a1_post1, a1_post2 ⟩ ← mul_internal_spec
  let* ⟨ ab, ab_post1, ab_post2, ab_post3 ⟩ ← montgomery_reduce_spec
  let* ⟨ a2, a2_post1, a2_post2 ⟩ ← mul_internal_spec
  · unfold constants.RR; decide
  let* ⟨ result, result_post1, result_post2, result_post3 ⟩ ← montgomery_reduce_spec
  · -- Scalar52_wide_as_Nat a2 < R * L
    -- ab < L (from montgomery_reduce), RR < L (concrete constant), so ab * RR < L * L < R * L
    rw [a2_post1]
    have h_RR_lt : Scalar52_as_Nat constants.RR < L := by
      unfold constants.RR Scalar52_as_Nat L; decide
    calc Scalar52_as_Nat ab * Scalar52_as_Nat constants.RR
        < L * L := by exact Nat.mul_lt_mul_of_lt_of_lt ab_post3 h_RR_lt
      _ < R * L := by exact Nat.mul_lt_mul_of_pos_right (by unfold R L; omega) (by unfold L; omega)
  refine ⟨?_, by assumption, by grind⟩
  have h_res_R_ab_RR : Scalar52_as_Nat result * R ≡
    Scalar52_as_Nat ab * Scalar52_as_Nat constants.RR [MOD L] := by
      rw [a2_post1] at result_post1
      rw [Nat.ModEq]
      exact result_post1
  have h_res_R_ab_R_R : Scalar52_as_Nat result * R ≡ Scalar52_as_Nat ab * R * R [MOD L] := by
    have := curve25519_dalek.backend.serial.u64.constants.RR_spec
    grind [Nat.ModEq, Nat.mul_mod, Nat.pow_two, Nat.mul_assoc]
  have h_res_R_a1_R : Scalar52_as_Nat result * R ≡ Scalar52_wide_as_Nat a1 * R  [MOD L] := by
    rw [← Nat.ModEq] at ab_post1
    have h_temp : Scalar52_as_Nat ab * R * R ≡ Scalar52_wide_as_Nat a1 * R [MOD L] := by
      exact Nat.ModEq.mul_right R ab_post1
    exact Nat.ModEq.trans h_res_R_ab_R_R h_temp
  have h_res_R_a_b_R : Scalar52_as_Nat result * R ≡
    Scalar52_as_Nat a * Scalar52_as_Nat b * R  [MOD L] := by
      rw [a1_post1] at h_res_R_a1_R
      exact h_res_R_a1_R
  grind [cancelR]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
