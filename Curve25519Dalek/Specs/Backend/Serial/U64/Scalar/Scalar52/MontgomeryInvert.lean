/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomerySquare
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.SquareMultiply

import Mathlib.Data.Int.ModEq
import PrimeCert.PrimeList

/-! # Spec Theorem for `Scalar52::montgomery_invert`

Specification and proof for `Scalar52::montgomery_invert`.

This function computes the multiplicative inverse using Montgomery form.

**Source**: curve25519-dalek/src/scalar.rs

-/

instance : Fact (Nat.Prime L) := ⟨by
  -- This is a known prime (2^252 + ...). TODO: find PrimeCert proof
  sorry
⟩

open Aeneas.Std Result curve25519_dalek.backend.serial.u64.scalar curve25519_dalek.backend.serial.u64.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar52

set_option maxHeartbeats 2000000 in
set_option exponentiation.threshold 262 in

/-
natural language description:

    • Takes as input an UnpackedScalar u that is assumed to be
      in Montgomery form. Then efficiently computes and returns an
      UnpackedScalar u' (also in Montgomery form) that represents
      the multiplicative inverse of u with respect to Montgomery multiplication.

    • This means: if we apply Montgomery multiplication to u and u',
      we get the Montgomery representation of 1, which is R mod L.

natural language specs:

    • For any UnpackedScalar u in Montgomery form with scalar_to_nat(u) ≢ 0 (mod L):
      - The function returns successfully with result u'
      - (Scalar52_as_Nat u * Scalar52_as_Nat u') mod L = R² mod L
      - This is equivalent to: montgomery_mul(u, u') = R mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.montgomery_invert`**:
- Precondition: u must be non-zero modulo L (i.e., represent a non-zero value in Montgomery form)
- No panic (always returns successfully for non-zero inputs)
- The result u' satisfies the property that Montgomery multiplication of u and u'
  yields R mod L (the Montgomery representation of 1)
-/
@[progress]
theorem montgomery_invert_spec (u : Scalar52) (h : Scalar52_as_Nat u % L ≠ 0)
    (h_bounds : ∀ i < 5, u[i]!.val < 2 ^ 62) :
    ∃ u', montgomery_invert u = ok u' ∧
    (Scalar52_as_Nat u * Scalar52_as_Nat u') % L = (R * R) % L := by
  unfold montgomery_invert

  progress*
  unfold pow2 at *


  have hR_inv : Invertible (R : ZMod L) := by
    apply invertibleOfCoprime
    unfold R
    rw [Nat.coprime_pow_left_iff (n := 260) (by decide)]
    rw [Nat.coprime_two_left]
    try decide

  simp only [*] at *

  repeat rw [← ZMod.natCast_eq_natCast_iff (c := L)] at *
  simp only [Nat.cast_mul] at *

  have hL_gt_1 : 1 < L := by
    unfold L; try decide
  letI : Fact (1 < L) := ⟨hL_gt_1⟩ -- Essential for Nontrivial
  letI : Invertible (R : ZMod L) := hR_inv

  have hR_ne_zero : (R : ZMod L) ≠ 0 := IsUnit.ne_zero (isUnit_of_invertible (R : ZMod L))
  -- 4. Create a specific rewrite rule for R and its powers
  -- This lemma says: "If x * R^n = y, then x = y * (R^n)⁻¹"
  -- It automatically handles R, R^2, R^8 etc. because R^1 = R.
  have h_iso (n : ℕ) (x y : ZMod L) : x * (R : ZMod L) ^ n = y ↔ x = y * ((R : ZMod L) ^ n)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero n hR_ne_zero)).symm

  simp only [h_iso] at *
  field_simp [hR_ne_zero] at *

  try ring_nf
  apply (ZMod.natCast_eq_natCast_iff (Scalar52_as_Nat u * Scalar52_as_Nat res) (R * R) L).mp
  push_cast

  field_simp

  group

  -- have hL_prime : Fact (Nat.Prime L) := ⟨by sorry⟩
  -- rw [ZMod.pow_card_sub_one_eq_one hL_prime (Scalar52_as_Nat u)]

  sorry
  -- progress as ⟨h1, h1_eq, h1_bnds⟩
  -- progress as ⟨h2, h2_eq, h2_bnds⟩
  -- progress as ⟨h3, h3_eq, h3_bnds⟩
  -- progress as ⟨h4, h4_eq, h4_bnds⟩
  -- progress as ⟨h5, h5_eq, h5_bnds⟩
  -- progress as ⟨h6, h6_eq, h6_bnds⟩
  -- progress as ⟨h7, h7_eq, h7_bnds⟩
  -- progress as ⟨h8, h8_eq, h8_bnds⟩
  -- progress as ⟨h9, h9_eq, h9_bnds⟩
  -- progress as ⟨h10, h10_eq⟩


  -- simp only [*] at y26_post_2 y25_post_1 y24_post_2 y23_post_1 y22_post_1 y21_post_1
  -- simp only [*] at y20_post_1 y19_post_1 y18_post_1 y17_post_1 y16_post_1 y15_post_1 y14_post_1
  -- simp only [*] at y13_post_1 y12_post_1 y11_post_1 y10_post_2 y9_post_1 y8_post_1 y7_post_1 y6_post_2
  -- simp only [*] at y5_post_2 y4_post_1 y3_post_1 y2_post_1 y1_post_1

  -- simp only [*] at res_post_1

  -- try ring_nf at res_post_1 y26_post_2 y25_post_1 y24_post_2 y23_post_1 y22_post_1 y21_post_1
  -- try ring_nf at y20_post_1 y19_post_1 y18_post_1 y17_post_1 y16_post_1 y15_post_1 y14_post_1
  -- try ring_nf at y13_post_1 y12_post_1 y11_post_1 y10_post_2 y9_post_1 y8_post_1 y7_post_1 y6_post_2
  -- try ring_nf at y5_post_2 y4_post_1 y3_post_1 y2_post_1 y1_post_1

  -- try ring_nf at res_post_1




end curve25519_dalek.scalar.Scalar52
