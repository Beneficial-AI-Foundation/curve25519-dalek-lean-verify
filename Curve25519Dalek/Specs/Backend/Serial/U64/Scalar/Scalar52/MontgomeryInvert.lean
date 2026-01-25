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

instance : Fact (Nat.Prime L) := by
  unfold L
  exact ⟨PrimeCert.prime_ed25519_order⟩



open Aeneas
open scoped Aeneas
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
    montgomery_invert u ⦃ u' =>
      (Scalar52_as_Nat u * Scalar52_as_Nat u') % L = (R * R) % L ∧
      (∀ i < 5, u'[i]!.val < 2 ^ 62) ⦄ := by
  sorry

end curve25519_dalek.scalar.Scalar52
