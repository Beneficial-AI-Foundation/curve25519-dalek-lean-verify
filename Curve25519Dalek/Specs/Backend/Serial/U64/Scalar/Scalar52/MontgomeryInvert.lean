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
open ZMod

namespace curve25519_dalek.scalar.Scalar52

section MontgomeryInvert_Helpers

/-- The Invariant: x is the Montgomery representation of u^k.
    Algebraically: x = u^k * R^(1-k) -/
def IsMont (R : ZMod L) (u_val : ZMod L) (x : ZMod L) (k : ℕ) : Prop :=
  x = u_val ^ k * R ^ (1 - (k : Int))

/-- Lemma: Montgomery Multiplication preserves the invariant.
    If x ~ u^k and y ~ u^j, then (x * y * R⁻¹) ~ u^(k+j) -/
lemma isMont_mul (R : ZMod L) (hR : R ≠ 0) {u_val x y res : ZMod L} {k j : ℕ}
    (hx : IsMont R u_val x k) (hy : IsMont R u_val y j)
    (h_eq : res = x * y * R⁻¹) :
    IsMont R u_val res (k + j) := by
  unfold IsMont at *
  rw [h_eq, hx, hy]; field_simp [hR]; generalize h_r : R = r
  have hr_ne_zero : r ≠ 0 := by rw [← h_r]; exact hR
  try ring_nf; rw [mul_assoc, ← pow_add, mul_assoc]

  -- Refine to peel off the 'u' part
  refine congr_arg₂ (· * ·) rfl ?_
  nth_rw 3 [← zpow_one r]; rw [← zpow_add₀ hr_ne_zero]; rw [← zpow_add₀ hr_ne_zero];
  apply congr_arg; simp only [Nat.cast_add]; try ring

/-- Lemma: Montgomery Squaring preserves the invariant. -/
lemma isMont_sq (R : ZMod L) (hR : R ≠ 0) {u_val x res : ZMod L} {k : ℕ}
    (hx : IsMont R u_val x k)
    (h_eq : res = x * x * R⁻¹) :
    IsMont R u_val res (2 * k) := by
  have := isMont_mul R hR hx hx h_eq; have h_subst : k + k = 2 * k := by ring;
  rwa [h_subst] at this

/-- Lemma: The Square-Multiply Loop step preserves the invariant. -/
lemma isMont_loop (R : ZMod L) (hR : R ≠ 0) {u_val y x res : ZMod L} {k j N : ℕ}
    (hy : IsMont R u_val y k) (hx : IsMont R u_val x j)
    (h_eq : res = y ^ N * x * (R ^ N)⁻¹) :
    IsMont R u_val res (k * N + j) := by
  unfold IsMont at *
  rw [h_eq, hy, hx]
  field_simp [hR]
  generalize h_r : R = r
  have hr_ne_zero : r ≠ 0 := by rw [← h_r]; exact hR

  --simp only rw [zpow_natCast];
  try ring_nf

  rw [← pow_add, mul_assoc, mul_assoc]
  refine congr_arg₂ (· * ·) ?_ ?_
  · apply congr_arg; ring
  · --
    rw [← zpow_natCast (r ^ _)]; rw [← zpow_mul, ← zpow_add₀ hr_ne_zero]
    nth_rw 1 [← zpow_natCast r]; rw [← zpow_add₀ hr_ne_zero]
    apply congr_arg; simp only [Nat.cast_add, Nat.cast_mul]; try ring

end MontgomeryInvert_Helpers



set_option maxHeartbeats 2000000 in -- progress* failed with normal heartbeats
set_option exponentiation.threshold 262 in
set_option maxRecDepth 3000 in -- otherwise the run_loop calls are too deep

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

  simp only [*] at *
  simp only [Nat.reduceAdd, Nat.reducePow] at *

  -- 1. Setup
  have hL_gt_1 : 1 < L := by unfold L; try decide
  letI : Fact (Nat.Prime L) := ⟨by sorry⟩ -- TODO: find PrimeCert proof
  letI : Fact (1 < L) := ⟨hL_gt_1⟩

  have hR_inv : Invertible (R : ZMod L) := by
    apply invertibleOfCoprime
    unfold R
    rw [Nat.coprime_pow_left_iff (n := 260) (by decide)]
    rw [Nat.coprime_two_left]
    exact Nat.Prime.odd_of_ne_two (Fact.out) (by unfold L; decide)
  letI : Invertible (R : ZMod L) := hR_inv
  have hR_ne_zero : (R : ZMod L) ≠ 0 := IsUnit.ne_zero (isUnit_of_invertible _)

  -- 2. OPTIMIZATION: Generalize Variables
  generalize h_uZ : (Scalar52_as_Nat u : ZMod L) = uZ
  generalize h_RZ : (R : ZMod L) = RZ

  have hRZ_ne_zero : RZ ≠ 0 := by rw [← h_RZ]; exact hR_ne_zero;

  -- 3. Define Helpers (Using the opaque uZ and RZ)
  -- Helper for Multiplication (Nat ModEq)
  have run_mul (x y res : Scalar52) (k j : ℕ)
      (hx : IsMont RZ uZ (Scalar52_as_Nat x) k)
      (hy : IsMont RZ uZ (Scalar52_as_Nat y) j)
      (h_post : Scalar52_as_Nat x * Scalar52_as_Nat y ≡ Scalar52_as_Nat res * R [MOD L]) :
      IsMont RZ uZ (Scalar52_as_Nat res) (k + j) := by
    apply isMont_mul RZ hRZ_ne_zero hx hy
    apply (ZMod.natCast_eq_natCast_iff _ _ L).mpr at h_post; push_cast at h_post
    rw [h_RZ] at h_post; rw [eq_mul_inv_iff_mul_eq₀ hRZ_ne_zero, ← h_post]

  -- Helper for Squaring (Strict Equality)
  have run_sq (x res : Scalar52) (k : ℕ)
      (hx : IsMont RZ uZ (Scalar52_as_Nat x) k)
      (h_post : Scalar52_as_Nat x * Scalar52_as_Nat x % L = Scalar52_as_Nat res * R % L) :
      IsMont RZ uZ (Scalar52_as_Nat res) (2 * k) := by
    apply isMont_sq RZ hRZ_ne_zero hx
    apply (ZMod.natCast_eq_natCast_iff _ _ L).mpr at h_post; push_cast at h_post
    rw [h_RZ] at h_post; rw [eq_mul_inv_iff_mul_eq₀ hRZ_ne_zero, ← h_post]

  -- Helper for Loops (Input: Nat Modulo Equality)
  have run_loop_nat (y x res : Scalar52) (k j N : ℕ)
      (hy : IsMont RZ uZ (Scalar52_as_Nat y) k)
      (hx : IsMont RZ uZ (Scalar52_as_Nat x) j)
      (h_post : (Scalar52_as_Nat res * R ^ N) % L = (Scalar52_as_Nat y ^ N * Scalar52_as_Nat x) % L) :
      IsMont RZ uZ (Scalar52_as_Nat res) (k * N + j) := by
    apply isMont_loop RZ hRZ_ne_zero hy hx
    apply (ZMod.natCast_eq_natCast_iff _ _ L).mpr at h_post; push_cast at h_post
    rw [h_RZ] at h_post; rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero N hRZ_ne_zero), h_post]

  -- Helper for Loops (ZMod Equality)
  have run_loop_zmod (y x res : Scalar52) (k j N : ℕ)
      (hy : IsMont RZ uZ (Scalar52_as_Nat y) k)
      (hx : IsMont RZ uZ (Scalar52_as_Nat x) j)
      (h_post : (Scalar52_as_Nat res : ZMod L) = (Scalar52_as_Nat y : ZMod L) ^ N * (Scalar52_as_Nat x : ZMod L) * (RZ ^ N)⁻¹) :
      IsMont RZ uZ (Scalar52_as_Nat res) (k * N + j) := by
    apply isMont_loop RZ hRZ_ne_zero hy hx
    exact h_post

  -- 4. Walk the Chain
  have step_u : IsMont RZ uZ (Scalar52_as_Nat u) 1 := by
    unfold IsMont; simp only [Nat.cast_one, sub_self, zpow_zero, mul_one, pow_one]; rw [h_uZ]

  -- Pre-computation
  have step_10   := run_sq u   _10   1 step_u   _10_post_1
  have step_100  := run_sq _10 _100  2 step_10  _100_post_1

  have step_11   := run_mul _10  u     _11   2 1 step_10 step_u    _11_post_1
  have step_101  := run_mul _10  _11   _101  2 3 step_10 step_11   _101_post_1
  have step_111  := run_mul _10  _101  _111  2 5 step_10 step_101  _111_post_1
  have step_1001 := run_mul _10  _111  _1001 2 7 step_10 step_111  _1001_post_1
  have step_1011 := run_mul _10  _1001 _1011 2 9 step_10 step_1001 _1011_post_1
  have step_1111 := run_mul _100 _1011 _1111 4 11 step_100 step_1011 _1111_post_1

  have step_y    := run_mul _1111 u y 15 1 step_1111 step_u y_post_1


  -- SPECIAL HANDLING FOR y1
  generalize h_huge : 85070591730234615865843651857942052864 = N_huge

  -- Rewrite the hypothesis y1_post_1 to use N_huge
  -- This prevents 'run_loop_nat' from seeing the massive number
  have y1_post_safe : Scalar52_as_Nat y1 * R ^ N_huge % L = Scalar52_as_Nat y ^ N_huge * Scalar52_as_Nat _101 % L := by
    rw [← h_huge]
    exact y1_post_1

  -- Run y1 with the abstract N_huge
  have step_y1 := run_loop_nat y _101 y1 16 5 N_huge step_y step_101 y1_post_safe


  -- THE REST OF THE CHAIN (Small Exponents)
  have step_y2  := run_loop_nat y1 _11 y2 _ 3 16 step_y1 step_11 y2_post_1
  have step_y3  := run_loop_nat y2  _1111 y3  _  15 32 step_y2  step_1111 y3_post_1
  have step_y4  := run_loop_nat y3  _1111 y4  _  15 32 step_y3  step_1111 y4_post_1
  have step_y5  := run_loop_nat y4  _1001 y5  _  9  16 step_y4  step_1001 y5_post_2
  have step_y6  := run_loop_nat y5  _11   y6  _  3  4  step_y5  step_11   y6_post_2
  have step_y7  := run_loop_nat y6  _1111 y7  _  15 32 step_y6  step_1111 y7_post_1
  have step_y8  := run_loop_nat y7  _101  y8  _  5  16 step_y7  step_101  y8_post_1
  have step_y9  := run_loop_nat y8  _101  y9  _  5  64 step_y8  step_101  y9_post_1
  have step_y10 := run_loop_nat y9  _111  y10 _  7  8  step_y9  step_111  y10_post_2
  have step_y11 := run_loop_nat y10 _1111 y11 _  15 32 step_y10 step_1111 y11_post_1
  have step_y12 := run_loop_nat y11 _111  y12 _  7  32 step_y11 step_111  y12_post_1
  have step_y13 := run_loop_nat y12 _11   y13 _  3  16 step_y12 step_11   y13_post_1
  have step_y14 := run_loop_nat y13 _1011 y14 _  11 32 step_y13 step_1011 y14_post_1
  have step_y15 := run_loop_nat y14 _1011 y15 _  11 64 step_y14 step_1011 y15_post_1
  have step_y16 := run_loop_nat y15 _1001 y16 _  9  1024 step_y15 step_1001 y16_post_1
  have step_y17 := run_loop_nat y16 _11   y17 _  3  16  step_y16 step_11   y17_post_1
  have step_y18 := run_loop_nat y17 _11   y18 _  3  32  step_y17 step_11   y18_post_1
  have step_y19 := run_loop_nat y18 _11   y19 _  3  32  step_y18 step_11   y19_post_1
  have step_y20 := run_loop_nat y19 _1001 y20 _  9  32  step_y19 step_1001 y20_post_1
  have step_y21 := run_loop_nat y20 _111  y21 _  7  16  step_y20 step_111  y21_post_1
  have step_y22 := run_loop_nat y21 _1111 y22 _  15 64  step_y21 step_1111 y22_post_1
  have step_y23 := run_loop_nat y22 _1011 y23 _  11 32  step_y22 step_1011 y23_post_1
  have step_y24 := run_loop_nat y23 _101  y24 _  5  8   step_y23 step_101  y24_post_2
  have step_y25 := run_loop_nat y24 _1111 y25 _  15 64  step_y24 step_1111 y25_post_1
  have step_y26 := run_loop_nat y25 _101  y26 _  5  8   step_y25 step_101  y26_post_2

  have step_res := run_loop_nat y26 _11 res _ 3 8 step_y26 step_11 res_post_1

  -- =========================================================
  -- 3. CONCLUSION
  -- =========================================================

  -- The Goal: u * res = R * R
  -- Substitute 'res' with 'u^K * R^(1-K)'
  unfold IsMont at step_res
  apply (ZMod.natCast_eq_natCast_iff _ _ L).mp; push_cast
  rw [h_uZ, h_RZ, step_res]
  -- Restore N_huge to calculate the exponent K
  have h_eqn : N_huge = 2^126 := by rw [← h_huge]; norm_num
  rw [h_eqn]

  have h_exp_val :
    (((((((((((((((((((((((((((16 * 2^126 + 5)
    * 16 + 3) * 32 + 15) * 32 + 15) * 16 + 9) * 4 + 3) * 32 + 15) * 16 + 5) * 64 + 5)
    * 8 + 7) * 32 + 15) * 32 + 7) * 16 + 3) * 32 + 11) * 64 + 11) * 1024 + 9) * 16 + 3) * 32 + 3)
    * 32 + 3) * 32 + 9) * 16 + 7) * 64 + 15) * 32 + 11) * 8 + 5) * 64 + 15) * 8 + 5) * 8 + 3)
    = L - 2 := by rw [L]; norm_num

  rw [h_exp_val]

  -- Final Algebraic Simplification
  -- uZ * (uZ^(L-2) * RZ^(1-(L-2))) = RZ^2
  -- a. Combine uZ
  -- uZ * uZ^(L-2) = uZ^(1 + L - 2) = uZ^(L-1)
  rw [← mul_assoc, ← pow_succ']
  have h_fermat_exp : L - 2 + 1 = L - 1 := by rw [L]; norm_num
  rw [h_fermat_exp]

  -- b. Apply Fermat's Little Theorem: uZ^(L-1) = 1
  -- We need to prove uZ != 0
  rw [← h_uZ]
  have hu_ne : (Scalar52_as_Nat u : ZMod L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod L) L, Nat.dvd_iff_mod_eq_zero]; exact h
  rw [ZMod.pow_card_sub_one_eq_one hu_ne]
  rw [one_mul]

  -- Simplify RZ exponent: RZ^(1 - (L-2)) = RZ^2
  rw [← pow_two]
  have h_exp : 1 - ↑(L - 2) = (3 : ℤ) - ↑L := by
    have h_ge : 2 ≤ L := by decide; -- Prove L is large enough symbolically (avoids computation)
    rw [Int.ofNat_sub h_ge] -- This prevents Lean from trying to compute (L - 2) in Nat
    try ring

  rw [h_exp, sub_eq_add_neg, zpow_add₀ hRZ_ne_zero, zpow_neg]; simp only [zpow_natCast, pow_card]
  field_simp




  /-
  -- The Square-Multiply Chain
  -- Note: We pass N = 2^(iterations). Lean unifies this with the raw number.
  have step_y1  := run_loop y   y1  _101  16 5  (2^126) step_y   step_101  y1_post_2 -- Check _post_2 in your view
  have step_y2  := run_loop y1  _11 y2    _  3  (2^4)   step_y1  step_11   y2_post_2
  have step_y3  := run_loop y2  _1111 y3  _  15 (2^5)   step_y2  step_1111 y3_post_2
  have step_y4  := run_loop y3  _1111 y4  _  15 (2^5)   step_y3  step_1111 y4_post_2
  have step_y5  := run_loop y4  _1001 y5  _  9  (2^4)   step_y4  step_1001 y5_post_1
  have step_y6  := run_loop y5  _11   y6  _  3  (2^2)   step_y5  step_11   y6_post_1
  have step_y7  := run_loop y6  _1111 y7  _  15 (2^5)   step_y6  step_1111 y7_post_2
  have step_y8  := run_loop y7  _101  y8  _  5  (2^4)   step_y7  step_101  y8_post_2
  have step_y9  := run_loop y8  _101  y9  _  5  (2^6)   step_y8  step_101  y9_post_2
  have step_y10 := run_loop y9  _111  y10 _  7  (2^3)   step_y9  step_111  y10_post_1
  have step_y11 := run_loop y10 _1111 y11 _  15 (2^5)   step_y10 step_1111 y11_post_2
  have step_y12 := run_loop y11 _111  y12 _  7  (2^5)   step_y11 step_111  y12_post_2
  have step_y13 := run_loop y12 _11   y13 _  3  (2^4)   step_y12 step_11   y13_post_2
  have step_y14 := run_loop y13 _1011 y14 _  11 (2^5)   step_y13 step_1011 y14_post_2
  have step_y15 := run_loop y14 _1011 y15 _  11 (2^6)   step_y14 step_1011 y15_post_2
  have step_y16 := run_loop y15 _1001 y16 _  9  (2^10)  step_y15 step_1001 y16_post_2
  have step_y17 := run_loop y16 _11   y17 _  3  (2^4)   step_y16 step_11   y17_post_2
  have step_y18 := run_loop y17 _11   y18 _  3  (2^5)   step_y17 step_11   y18_post_2
  have step_y19 := run_loop y18 _11   y19 _  3  (2^5)   step_y18 step_11   y19_post_2
  have step_y20 := run_loop y19 _1001 y20 _  9  (2^5)   step_y19 step_1001 y20_post_2
  have step_y21 := run_loop y20 _111  y21 _  7  (2^4)   step_y21 step_111  y21_post_2
  have step_y22 := run_loop y21 _1111 y22 _  15 (2^6)   step_y21 step_1111 y22_post_2
  have step_y23 := run_loop y22 _1011 y23 _  11 (2^5)   step_y22 step_1011 y23_post_2
  have step_y24 := run_loop y23 _101  y24 _  5  (2^3)   step_y23 step_101  y24_post_1
  have step_y25 := run_loop y24 _1111 y25 _  15 (2^6)   step_y24 step_1111 y25_post_2
  have step_y26 := run_loop y25 _101  y26 _  5  (2^3)   step_y25 step_101  y26_post_1

  -- Final Result
  have step_res := run_loop y26 _11 res _ 3 (2^3) step_y26 step_11 res_post_2
  -/





/-
  ============================================
  OLD 2 PROOF ATTEMPT
  ============================================
@[progress]
theorem montgomery_invert_spec (u : Scalar52) (h : Scalar52_as_Nat u % L ≠ 0)
    (h_bounds : ∀ i < 5, u[i]!.val < 2 ^ 62) :
    ∃ u', montgomery_invert u = ok u' ∧
    (Scalar52_as_Nat u * Scalar52_as_Nat u') % L = (R * R) % L := by
  unfold montgomery_invert
  progress*
  unfold pow2 at *

  -- 1. Setup L as Prime (Makes ZMod L a Field)
  have hL_gt_1 : 1 < L := by unfold L; try decide
  letI : Fact (Nat.Prime L) := ⟨by sorry⟩ -- Essential for Field instance
  letI : Fact (1 < L) := ⟨hL_gt_1⟩

  -- 2. Setup R Invertibility
  have hR_inv : Invertible (R : ZMod L) := by
    apply invertibleOfCoprime
    unfold R
    rw [Nat.coprime_pow_left_iff (n := 260) (by decide)]
    rw [Nat.coprime_two_left]
    exact Nat.Prime.odd_of_ne_two (Fact.out) (by unfold L; decide)
  letI : Invertible (R : ZMod L) := hR_inv
  have hR_ne_zero : (R : ZMod L) ≠ 0 := IsUnit.ne_zero (isUnit_of_invertible _)

  -- 3. Lift from Nat to ZMod L
  apply (ZMod.natCast_eq_natCast_iff (Scalar52_as_Nat u * Scalar52_as_Nat res) (R * R) L).mp
  push_cast

  have lift_to_zmod (a b : ℕ) : a % L = b % L ↔ (a : ZMod L) = (b : ZMod L) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact Eq.to_iff rfl

  simp only [lift_to_zmod] at *
  simp only [Nat.cast_mul, Nat.cast_pow] at *

  -- 4. Isolate Variables
  -- Case A: R^n * x = y  ->  x = y * R^-n
  have h_iso_L (n : ℕ) (x y : ZMod L) : (R : ZMod L) ^ n * x = y ↔ x = y * ((R : ZMod L) ^ n)⁻¹ := by
    rw [mul_comm ((R : ZMod L)^n), eq_mul_inv_iff_mul_eq₀]
    apply pow_ne_zero; exact hR_ne_zero

  -- Case B: x * R^n = y  ->  x = y * R^-n
  have h_iso_R (n : ℕ) (x y : ZMod L) : x * (R : ZMod L) ^ n = y ↔ x = y * ((R : ZMod L) ^ n)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀]
    apply pow_ne_zero; exact hR_ne_zero

  -- Case C: Simple R * x = y (Captures n=1 cases that matching might miss)
  have h_iso_L1 (x y : ZMod L) : (R : ZMod L) * x = y ↔ x = y * (R : ZMod L)⁻¹ := by
    rw [mul_comm, eq_mul_inv_iff_mul_eq₀ hR_ne_zero]

  -- Case D: Simple x * R = y
  have h_iso_R1 (x y : ZMod L) : x * (R : ZMod L) = y ↔ x = y * (R : ZMod L)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hR_ne_zero]

  simp only [*] at *
  simp only [Nat.reduceAdd, Nat.reducePow] at *

  -- 5. Define Lifting Helpers
  let uZ : ZMod L := Scalar52_as_Nat u
  let RZ : ZMod L := R


  have run_mul (x y res : Scalar52) (k j : ℕ)
      (hx : IsMont RZ uZ (Scalar52_as_Nat x) k)
      (hy : IsMont RZ uZ (Scalar52_as_Nat y) j)
      (h_post : Scalar52_as_Nat x * Scalar52_as_Nat y ≡ Scalar52_as_Nat res * R [MOD L]) :
      IsMont RZ uZ (Scalar52_as_Nat res) (k + j) := by
    apply isMont_mul RZ hR_ne_zero hx hy
    -- Lift Nat.ModEq to ZMod equality
    apply (ZMod.natCast_eq_natCast_iff _ _ L).mpr at h_post
    push_cast at h_post
    -- Goal: res = x * y * RZ⁻¹
    -- Hyp:  x * y = res * R
    rw [eq_mul_inv_iff_mul_eq₀ hR_ne_zero]
    rw [← h_post]

  -- have run_mul' (x y res : Scalar52) (k j : ℕ)
  --     (hx : IsMont RZ uZ (Scalar52_as_Nat x) k)
  --     (hy : IsMont RZ uZ (Scalar52_as_Nat y) j)
  --     (h_post : (Scalar52_as_Nat x : ZMod L) * (Scalar52_as_Nat y : ZMod L) = (Scalar52_as_Nat res : ZMod L) * (R : ZMod L)) :
  --     IsMont RZ uZ (Scalar52_as_Nat res) (k + j) := by
  --   apply isMont_mul RZ hR_ne_zero hx hy
  --   rw [eq_mul_inv_iff_mul_eq₀ hR_ne_zero]
  --   rw [← h_post]

  -- have run_sq (x res : Scalar52) (k : ℕ)
  --     (hx : IsMont RZ uZ (Scalar52_as_Nat x) k)
  --     (h_post : Scalar52_as_Nat x * Scalar52_as_Nat x = Scalar52_as_Nat res * R) :
  --     IsMont RZ uZ (Scalar52_as_Nat res) (2 * k) := by
  --   apply isMont_sq RZ hR_ne_zero hx
  --   -- Lift strict Nat equality to ZMod equality
  --   apply congr_arg (Nat.cast : ℕ → ZMod L) at h_post
  --   simp only [Nat.cast_mul] at h_post
  --   -- Goal: res = x * x * RZ⁻¹
  --   rw [eq_mul_inv_iff_mul_eq₀ hR_ne_zero]
  --   rw [← h_post]

  have run_sq' (x res : Scalar52) (k : ℕ)
      (hx : IsMont RZ uZ (Scalar52_as_Nat x) k)
      (h_post : (Scalar52_as_Nat x : ZMod L) * (Scalar52_as_Nat x : ZMod L) = (Scalar52_as_Nat res : ZMod L) * (R : ZMod L)) :
      IsMont RZ uZ (Scalar52_as_Nat res) (2 * k) := by
    apply isMont_sq RZ hR_ne_zero hx
    rw [eq_mul_inv_iff_mul_eq₀ hR_ne_zero]
    rw [← h_post]

  -- have run_loop (y x res : Scalar52) (k j N : ℕ)
  --     (hy : IsMont RZ uZ (Scalar52_as_Nat y) k)
  --     (hx : IsMont RZ uZ (Scalar52_as_Nat x) j)
  --     (h_post : (Scalar52_as_Nat res * R ^ N) % L = (Scalar52_as_Nat y ^ N * Scalar52_as_Nat x) % L) :
  --     IsMont RZ uZ (Scalar52_as_Nat res) (k * N + j) := by
  --   apply isMont_loop RZ hR_ne_zero hy hx
  --   apply (ZMod.natCast_eq_natCast_iff _ _ L).mpr at h_post; push_cast at h_post
  --   rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero N hR_ne_zero)]; rw [h_post]

  -- have run_loop' (y x res : Scalar52) (k j N : ℕ)
  --     (hy : IsMont RZ uZ (Scalar52_as_Nat y) k)
  --     (hx : IsMont RZ uZ (Scalar52_as_Nat x) j)
  --     (h_post : (Scalar52_as_Nat res : ZMod L) * ((R : ZMod L) ^ N) = (Scalar52_as_Nat y : ZMod L) ^ N * (Scalar52_as_Nat x : ZMod L)) :
  --     IsMont RZ uZ (Scalar52_as_Nat res) (k * N + j) := by
  --   apply isMont_loop RZ hR_ne_zero hy hx
  --   rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero N hR_ne_zero)]
  --   rw [h_post]

  -- ZMod loop helper
  -- Accepts: res = y^N * x * (R^N)⁻¹
  have run_loop_zmod (y x res : Scalar52) (k j N : ℕ)
      (hy : IsMont RZ uZ (Scalar52_as_Nat y) k)
      (hx : IsMont RZ uZ (Scalar52_as_Nat x) j)
      (h_post : (Scalar52_as_Nat res : ZMod L) = (Scalar52_as_Nat y : ZMod L) ^ N * (Scalar52_as_Nat x : ZMod L) * ((R : ZMod L) ^ N)⁻¹) :
      IsMont RZ uZ (Scalar52_as_Nat res) (k * N + j) := by
    apply isMont_loop RZ hR_ne_zero hy hx
    exact h_post

  -- 6. Walk the Chain of equivalences
  -- Base case: u is u^1 * R^(1-1)
  have step_u : IsMont RZ uZ (Scalar52_as_Nat u) 1 := by
    unfold IsMont; simp only [Nat.cast_one, sub_self, zpow_zero, mul_one, pow_one]; rfl

  -- Initial Pre-computation Phase
  have step_10   : IsMont RZ uZ (Scalar52_as_Nat _10)   2 := run_sq' u   _10   1 step_u   _10_post_1
  have step_100  : IsMont RZ uZ (Scalar52_as_Nat _100)  4 := run_sq' _10 _100  2 step_10  _100_post_1

  have step_11   : IsMont RZ uZ (Scalar52_as_Nat _11)   3 := run_mul _10  u     _11   2 1 step_10 step_u    _11_post_1
  have step_101  : IsMont RZ uZ (Scalar52_as_Nat _101)  5 := run_mul _10  _11   _101  2 3 step_10 step_11   _101_post_1
  have step_111  : IsMont RZ uZ (Scalar52_as_Nat _111)  7 := run_mul _10  _101  _111  2 5 step_10 step_101  _111_post_1
  have step_1001 : IsMont RZ uZ (Scalar52_as_Nat _1001) 9 := run_mul _10  _111  _1001 2 7 step_10 step_111  _1001_post_1
  have step_1011 : IsMont RZ uZ (Scalar52_as_Nat _1011) 11 := run_mul _10  _1001 _1011 2 9 step_10 step_1001 _1011_post_1
  have step_1111 : IsMont RZ uZ (Scalar52_as_Nat _1111) 15 := run_mul _100 _1011 _1111 4 11 step_100 step_1011 _1111_post_1

  -- y = u^16
  have step_y : IsMont RZ uZ (Scalar52_as_Nat y) 16 := run_mul _1111 u y 15 1 step_1111 step_u y_post_1

  -- SPECIAL HANDLING FOR y1
  generalize h_huge_lit : 85070591730234615865843651857942052864 = N_huge

  have h_eqn : N_huge = 2^126 := by
    rw [← h_huge_lit]
    norm_num

  have y1_post_abstract : (Scalar52_as_Nat y1 : ZMod L) = (Scalar52_as_Nat y) ^ N_huge * (Scalar52_as_Nat _101) * ((R : ZMod L) ^ N_huge)⁻¹ := by
    rw [← h_huge_lit]
    exact y1_post_1

  -- The Square-Multiply Chain
  have step_y1 := run_loop_zmod y _101 y1 16 5 (N_huge) step_y step_101 y1_post_abstract
  --have step_y2  := run_loop_zmod y1  _11   y2  _  3  (2^4)   step_y1  step_11   y2_post_1
  --have step_y3  := run_loop_zmod y2  _1111 y3  _  15 (2^5)   step_y2  step_1111 y3_post_2

-/


/-
  ============================================
  OLD 1 PROOF ATTEMPT
  ============================================
  @[progress]
  theorem montgomery_invert_spec (u : Scalar52) (h : Scalar52_as_Nat u % L ≠ 0)
    (h_bounds : ∀ i < 5, u[i]!.val < 2 ^ 62) :
    ∃ u', montgomery_invert u = ok u' ∧
    (Scalar52_as_Nat u * Scalar52_as_Nat u') % L = (R * R) % L := by
  unfold montgomery_invert
  progress*
  unfold pow2 at *

  -- 1. Setup L as Prime (Makes ZMod L a Field)
  have hL_gt_1 : 1 < L := by unfold L; try decide
  letI : Fact (Nat.Prime L) := ⟨by sorry⟩ -- Essential for Field instance
  letI : Fact (1 < L) := ⟨hL_gt_1⟩

  -- 2. Setup R Invertibility
  have hR_inv : Invertible (R : ZMod L) := by
    apply invertibleOfCoprime
    unfold R
    rw [Nat.coprime_pow_left_iff (n := 260) (by decide)]
    rw [Nat.coprime_two_left]
    exact Nat.Prime.odd_of_ne_two (Fact.out) (by unfold L; decide)
  letI : Invertible (R : ZMod L) := hR_inv
  have hR_ne_zero : (R : ZMod L) ≠ 0 := IsUnit.ne_zero (isUnit_of_invertible _)

  -- 3. Lift from Nat to ZMod L
  apply (ZMod.natCast_eq_natCast_iff (Scalar52_as_Nat u * Scalar52_as_Nat res) (R * R) L).mp
  push_cast

  have lift_to_zmod (a b : ℕ) : a % L = b % L ↔ (a : ZMod L) = (b : ZMod L) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact Eq.to_iff rfl

  simp only [lift_to_zmod] at *
  simp only [Nat.cast_mul, Nat.cast_pow] at *

  -- 4. Isolate Variables
  -- Case A: R^n * x = y  ->  x = y * R^-n
  have h_iso_L (n : ℕ) (x y : ZMod L) : (R : ZMod L) ^ n * x = y ↔ x = y * ((R : ZMod L) ^ n)⁻¹ := by
    rw [mul_comm ((R : ZMod L)^n), eq_mul_inv_iff_mul_eq₀]
    apply pow_ne_zero; exact hR_ne_zero

  -- Case B: x * R^n = y  ->  x = y * R^-n
  have h_iso_R (n : ℕ) (x y : ZMod L) : x * (R : ZMod L) ^ n = y ↔ x = y * ((R : ZMod L) ^ n)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀]
    apply pow_ne_zero; exact hR_ne_zero

  -- Case C: Simple R * x = y (Captures n=1 cases that matching might miss)
  have h_iso_L1 (x y : ZMod L) : (R : ZMod L) * x = y ↔ x = y * (R : ZMod L)⁻¹ := by
    rw [mul_comm, eq_mul_inv_iff_mul_eq₀ hR_ne_zero]

  -- Case D: Simple x * R = y
  have h_iso_R1 (x y : ZMod L) : x * (R : ZMod L) = y ↔ x = y * (R : ZMod L)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hR_ne_zero]

  simp only [*] at *
  simp only [Nat.reduceAdd, Nat.reducePow] at *


  -- "x is the Montgomery representation of u^k"
  -- Algebraically: x = u^k * R^(-(k-1)) = u^k * R^(1-k)
  let IsMont (x : ZMod L) (k : Nat) : Prop :=
    x = (Scalar52_as_Nat u : ZMod L) ^ k * (R : ZMod L) ^ (1 - (k : Int))

  -- Case 1: Simple Montgomery Multiplication (x * y * R⁻¹)
  have h_mont_mul : ∀ x k y j res,
      IsMont x k → IsMont y j →
      (res = x * y * (R : ZMod L)⁻¹) →
      IsMont res (k + j) := by
    intros x k y j res hx hy h_eq
    unfold IsMont at *; rw [h_eq, hx, hy]
    -- Generalize R -> r and simplify field ops
    field_simp [hR_ne_zero]; group; generalize h_r_def : (R : ZMod L) = r;
    have hr_ne_zero : r ≠ 0 := by rw [← h_r_def]; exact hR_ne_zero;
    simp only [zpow_natCast]; try ring_nf; rw [mul_assoc, ← pow_add, mul_comm r _, mul_assoc]
    -- Refine to peel off the 'u' part
    refine congr_arg₂ (· * ·) rfl ?_
    rw [← zpow_add₀ hr_ne_zero]; nth_rw 2 [← zpow_one r]; rw [← zpow_add₀ hr_ne_zero]
    apply congr_arg
    try ring

  -- Case 2: Simple Montgomery Squaring (x^2 * R⁻¹)
  have h_mont_sq : ∀ x k res,
      IsMont x k →
      (res = x * x * (R : ZMod L)⁻¹) →
      IsMont res (2 * k) := by
    intros x k res hx h_eq; have h_subst : k + k = 2 * k := by ring
    have h_eq' : IsMont res (k + k) := h_mont_mul x k x k res hx hx h_eq
    rwa [h_subst] at h_eq'

  -- Case 3: Square-Multiply Loops
  have h_loop_step : ∀ y k x j N res,
      IsMont y k → IsMont x j →
      (res = y ^ N * x * ((R : ZMod L) ^ N)⁻¹) →
      IsMont res (k * N + j) := by
    intros y k x j N res hy hx h_eq
    unfold IsMont at *
    rw [h_eq, hy, hx]
    field_simp [hR_ne_zero]; group; generalize h_r_def : (R : ZMod L) = r;
    have hr_ne_zero : r ≠ 0 := by rw [← h_r_def]; exact hR_ne_zero;
    simp only [zpow_natCast]; try ring_nf;
    rw [← pow_add, mul_assoc, mul_comm (r^N) _, mul_assoc]

    refine congr_arg₂ (· * ·) ?_ ?_
    · -- Solves u^(k*N+j) = u^(↑k*↑N+↑j)
      apply congr_arg; try ring
    · -- Solves (r^(1-k))^N * r^(1-j) = r^N * r^(...)
      rw [← zpow_natCast (r ^ _)]; rw [← zpow_mul, ← zpow_add₀ hr_ne_zero]
      nth_rw 1 [← zpow_natCast r]; rw [← zpow_add₀ hr_ne_zero]
      apply congr_arg; try ring

  -- 5. Walk the Chain
  -- 'u' satisfies IsMont u 1
  have step_u : IsMont (Scalar52_as_Nat u) 1 := by
    unfold IsMont; group;

  -- _10 = u^2
  have step_10 : IsMont (Scalar52_as_Nat _10) 2 := by
    apply h_mont_sq _ 1 _ step_u
    rw [← h_iso_L1];
    conv at _10_post_1 =>
      rhs
      rw [mul_comm]
    exact _10_post_1.symm

  -- _11 = _10 * u = u^3
  have step_11 : IsMont (Scalar52_as_Nat _11) 3 := by
    apply h_mont_mul _ 2 _ 1 _ step_10 step_u
    rw [← h_iso_R1, ← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
    exact _11_post_1.symm



  --simp only [h_iso_L, h_iso_R, h_iso_L1, h_iso_R1] at *

  sorry

-/

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
