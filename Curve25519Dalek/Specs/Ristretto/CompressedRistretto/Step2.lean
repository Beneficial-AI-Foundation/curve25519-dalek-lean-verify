/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Field.FieldElement51.IsZero
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EDWARDS_D
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE

/-! # Spec Theorem for `ristretto.decompress.step_2`

Specification and proof for `ristretto.decompress.step_2`.

This function performs the second step of Ristretto decompression, computing
the affine coordinates (x, y) of a point on the Edwards curve from the field element s, then
outputs extended Edwards coordinates (x, y, 1, xy)

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Edwards Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.math curve25519_dalek.ristretto
namespace curve25519_dalek.ristretto.decompress

/-- Standalone on-curve proof for decompression, extracted to avoid heartbeat
    timeout in the large proof context of step_2_spec. -/
private lemma on_curve_from_decompression {F : Type*} [Field F]
    (a d s I u1 u2 u7 : F)
    (ha : a = -1)
    (hu1 : u1 = 1 - s ^ 2)
    (hu2 : u2 = 1 + s ^ 2)
    (hu7 : u7 = -d * u1 ^ 2 - u2 ^ 2)
    (hI : I ^ 2 * (u7 * u2 ^ 2) = 1) :
    a * (2 * s * I * u2) ^ 2 + (u1 * (I ^ 2 * u2 * u7)) ^ 2 =
    1 + d * (2 * s * I * u2) ^ 2 * (u1 * (I ^ 2 * u2 * u7)) ^ 2 := by
  have h := decompress_helper a d s I u1 u2 u7 ha
    (by rw [hu1, ha]; ring) (by rw [hu2, ha]; ring)
    (by rw [hu7, ha]; ring) hI
  dsimp only at h
  linear_combination h

/-- Extract coordinates from a RistrettoPoint.toPoint with Z = ONE.
    Factored out to avoid whnf timeout from toPoint reduction in large contexts. -/
private lemma toPoint_coords {x y z t : FieldElement51}
    (h : edwards.EdwardsPoint.IsValid { X := x, Y := y, Z := z, T := t })
    (hz : z.toField = (1 : CurveField))
    {P : Point Ed25519}
    (h_pt : RistrettoPoint.toPoint { X := x, Y := y, Z := z, T := t } = P) :
    P.x = x.toField ∧ P.y = y.toField := by
  have hPxy := edwards.EdwardsPoint.toPoint_of_isValid h
  unfold RistrettoPoint.toPoint at h_pt
  constructor
  · rw [← h_pt, hPxy.1, hz, div_one]
  · rw [← h_pt, hPxy.2, hz, div_one]

/-- Combine P.x*P.y = t.toField with is_negative t.toField = false.
    Extracted to avoid whnf timeout from toField/is_negative reduction in large contexts. -/
private lemma is_negative_Pxy_false {x1 y t : FieldElement51} {P : Point Ed25519}
    {c : subtle.Choice}
    (hPx : P.x = x1.toField) (hPy : P.y = y.toField)
    (ht : t.toField = x1.toField * y.toField)
    (h_c : c.val = 0#u8)
    (h_post : c.val = 1#u8 ↔ Field51_as_Nat t % p % 2 = 1) :
    is_negative (P.x * P.y) = false := by
  have h1 : P.x * P.y = t.toField := by rw [hPx, hPy, ← ht]
  rw [h1]
  simp only [is_negative, FieldElement51.toField, ZMod.val_natCast,
    beq_eq_false_iff_ne]
  intro h
  exact absurd (h_post.mpr h) (by rw [h_c]; decide)

/-- P.y ≠ 0 from c1.val = 0 and the is_zero postcondition.
    Extracted to avoid timeout from ZMod unfolding in large contexts. -/
private lemma Py_ne_zero {y : FieldElement51} {P : Point Ed25519} {c1 : subtle.Choice}
    (hPy : P.y = y.toField)
    (h_c1 : c1.val = 0#u8)
    (h_post : c1.val = 1#u8 ↔ Field51_as_Nat y % p = 0) :
    P.y ≠ 0 := by
  rw [hPy]
  simp only [FieldElement51.toField, ne_eq, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  intro h
  exact absurd (h_post.mpr h) (by rw [h_c1]; decide)


/-- Wrapper for `decompress_step2_2` with the algebraic forms used in step_2_spec.
    Extracted to avoid ring normalization timeouts in the large proof context. -/
private lemma decompress_step2_backward (s I u1 u2 u7 : ZMod p)
    (hu1 : u1 = 1 - s ^ 2)
    (hu2 : u2 = 1 + s ^ 2)
    (hu7 : u7 = -Ed25519.d * u1 ^ 2 - u2 ^ 2)
    (hI : I ^ 2 * (u7 * u2 ^ 2) = 1)
    (pt : Point Ed25519)
    (h_neg : is_negative (pt.x * pt.y) = false)
    (h_y_ne : pt.y ≠ 0)
    (hx : pt.x = abs_edwards (2 * s * I * u2))
    (hy : pt.y = u1 * (I ^ 2 * u2 * u7)) :
    decompress_step2 s = some pt := by
  have hEd : Ed25519.d = (↑d : ZMod p) := rfl
  have h_u1_eq : (1 + a_val * s ^ 2) = u1 := by rw [hu1, a_val]; ring
  have h_u2_eq : (1 - a_val * s ^ 2) = u2 := by rw [hu2, a_val]; ring
  have h_v_eq : a_val * (↑d : ZMod p) * u1 ^ 2 - u2 ^ 2 = u7 := by
    rw [hu7, hEd, a_val]; ring
  apply decompress_step2_2 s pt I
  · rw [h_u1_eq, h_u2_eq, h_v_eq]; exact hI
  · exact h_neg
  · exact h_y_ne
  · rw [hx]; congr 1; rw [h_u2_eq]; ring
  · rw [h_u1_eq, h_u2_eq, h_v_eq, hy]; ring

/-- Forward wrapper for `decompress_step2_1`, converting a_val form to Ed25519.d form.
    Given decompress_step2 succeeds, we get IsSquare W, W ≠ 0, validation passes,
    and for any I with I²·W = 1 the point coordinates are determined.
    Proof bridges a_val = -1 and Ed25519.d = ↑d to decompress_step2_1. -/
private lemma decompress_step2_forward (s : ZMod p) (P : Point Ed25519)
    (h : decompress_step2 s = some P)
    (u1 u2 v W : ZMod p)
    (hu1 : u1 = 1 - s ^ 2)
    (hu2 : u2 = 1 + s ^ 2)
    (hv : v = -Ed25519.d * u1 ^ 2 - u2 ^ 2)
    (hW : W = v * u2 ^ 2) :
    IsSquare W ∧ W ≠ 0 ∧
    is_negative (P.x * P.y) = false ∧
    P.y ≠ 0 ∧
    (∀ I : ZMod p, I ^ 2 * W = 1 →
      P.x = abs_edwards (2 * s * I * u2) ∧
      P.y = u1 * (I ^ 2 * u2 * v)) := by
  have h_data := decompress_step2_1 s P h
  obtain ⟨h_sq', h_ne', h_neg', h_y_ne', h_Px', h_Py'⟩ := h_data
  -- Bridge between a_val form and Ed25519.d form
  have hEd : Ed25519.d = (↑d : ZMod p) := rfl
  have hu1' : (1 + a_val * s ^ 2) = u1 := by rw [hu1, a_val]; ring
  have hu2' : (1 - a_val * s ^ 2) = u2 := by rw [hu2, a_val]; ring
  have hv' : a_val * (↑d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
    (1 - a_val * s ^ 2) ^ 2 = v := by rw [hv, hEd, hu1, hu2, a_val]; ring
  have hW' : (a_val * (↑d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
    (1 - a_val * s ^ 2) ^ 2) * (1 - a_val * s ^ 2) ^ 2 = W := by
    rw [hW, hv, hEd, hu1, hu2, a_val]; ring
  -- Rewrite hypotheses to use u1, u2, v, W (order matters!)
  -- hW' first: replaces the full W-expression inside inv_sqrt_checked args
  rw [hW'] at h_sq' h_ne' h_neg' h_y_ne' h_Px' h_Py'
  -- hv' next: replaces the standalone v-expression (before hu1'/hu2' break it)
  rw [hv', hu1', hu2'] at h_neg' h_y_ne' h_Py'
  rw [hu2'] at h_Px'
  set I_math := (inv_sqrt_checked W).1 with hI_math_def
  -- Goals 1-4
  refine ⟨h_sq', h_ne', ?_, ?_, ?_⟩
  · -- is_negative (P.x * P.y) = false
    rw [h_Px', h_Py']; exact h_neg'
  · -- P.y ≠ 0
    rw [h_Py']; exact h_y_ne'
  · -- ∀ I, I^2 * W = 1 → coordinates match
    intro I hI_sq
    -- Get I_math^2 * W = 1 (uses combined lemma to avoid maxRecDepth)
    have hI_math_sq : I_math ^ 2 * W = 1 := inv_sqrt_checked_sq_mul W h_sq' h_ne'
    -- I^2 = I_math^2
    have hI_sq_eq : I ^ 2 = I_math ^ 2 :=
      mul_right_cancel₀ h_ne' (by rw [hI_sq, hI_math_sq])
    -- abs_edwards(-x) = abs_edwards(x) helper
    have abs_edwards_neg : ∀ (x : ZMod p), abs_edwards (-x) = abs_edwards x := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · unfold abs_edwards is_negative
        have h_neg_val : (-x : ZMod p).val = p - x.val := by
          rw [ZMod.neg_val]; exact if_neg hx
        rw [h_neg_val]
        have hxlt : x.val < p := x.val_lt
        have hp_odd : p % 2 = 1 := by decide
        have hxv : x.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
        have hxpos : 0 < x.val := Nat.pos_of_ne_zero hxv
        have h_par : (p - x.val) % 2 ≠ x.val % 2 := by omega
        by_cases hpx : x.val % 2 = 1
        · have : (p - x.val) % 2 = 0 := by omega
          simp only [beq_iff_eq] at *; simp [hpx, this]
        · have hpx0 : x.val % 2 = 0 := by omega
          have : (p - x.val) % 2 = 1 := by omega
          simp only [beq_iff_eq] at *; simp [hpx0, this]
    constructor
    · -- P.x = abs_edwards (2 * s * I * u2)
      rw [h_Px']
      -- Prove squares are equal via separate ring lemmas (avoids ring_nf unfolding I_math)
      have h_x_sq : (2 * s * I * u2) ^ 2 = (2 * s * (I_math * u2)) ^ 2 := by
        have h1 : (2 * s * I * u2) ^ 2 = 4 * s ^ 2 * I ^ 2 * u2 ^ 2 := by ring
        have h2 : (2 * s * (I_math * u2)) ^ 2 = 4 * s ^ 2 * I_math ^ 2 * u2 ^ 2 := by ring
        rw [h1, h2, hI_sq_eq]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h_x_sq with h_eq | h_neg
      · rw [h_eq]
      · rw [h_neg]; exact (abs_edwards_neg _).symm
    · -- P.y = u1 * (I^2 * u2 * v)
      rw [h_Py']
      -- Rewrite I_math * (I_math * u2) * v to I_math^2 * u2 * v, then to I^2 * u2 * v
      have h1 : I_math * (I_math * u2) * v = I_math ^ 2 * u2 * v := by ring
      rw [h1, ← hI_sq_eq]

/-
natural language description:

    • Takes a field element s as input (from step_1)
    • Computes ss = s²
    • Computes u1 = 1 - ss
    • Computes u2 = 1 + ss
    • Computes u2_sqr = u2²
    • Computes v = (-EDWARDS_D) · u1² - u2²
    • Computes I = invsqrt(v · u2²), obtaining (ok1, I) where ok1 indicates if the inverse square root exists
    • Computes Dx = I · u2
    • Computes Dy = I · Dx · v
    • Computes x = 2s · Dx
    • Conditionally negates x if x is negative, producing x1
    • Computes y = u1 · Dy
    • Computes t = x1 · y (the extended coordinate)
    • Checks if t is negative (stored in c)
    • Checks if y is zero (stored in c1)
    • Returns a tuple containing:
        - ok1: Choice indicating whether the inverse square root computation succeeded
        - c: Choice indicating whether t is negative
        - c1: Choice indicating whether y is zero
        - A RistrettoPoint with coordinates (X=x1, Y=y, Z=1, T=t) in extended twisted Edwards form

    This is the second step in Ristretto decompression. It computes the point coordinates
    from the field element s, performing the inverse of the Ristretto encoding map.
    The three Choice values (ok1, c, c1) are used in the full decompress function to validate
    that the decompression is valid.

natural language specs:

    • The function always succeeds (no panic) for any valid field element s
    • ok1 is true iff the inverse square root of w := v · u2² exists,
      where v = (-EDWARDS_D) · u1² - u2², u1 = 1 - s², u2 = 1 + s².
      The function called in step_2 is `invsqrt(w)`, which computes
      r = 1/√w. For 1/√w to exist we need w ≠ 0 (so that 1/w is
      defined) and w to be a quadratic residue (so that √w exists).
      Equivalently, `invsqrt` tests whether r² · w ≡ 1 (mod p) has a
      solution. When w = 0, r² · 0 = 0 ≠ 1, so no solution exists and
      ok1 = 0. Since Mathlib's `IsSquare 0 = True` (0 = 0²), the spec
      requires the conjunct `w ≠ 0` alongside `IsSquare w`.
    • c is true if and only if t is negative, where t = x1 · y is the T coordinate of the output point
    • c1 is true if and only if y = 0
    • The output point pt is a valid RistrettoPoint when ok1 = 1, c = 0, and c1 = 0 (all checks pass)
-/


set_option maxHeartbeats 400000 in -- needed for complex decompress step2 unfold
/-- **Spec for `step_2`**
Reflects the Rust implementation:
1.  Performs the algebraic lift (Elligator map) to compute a point `pt`.
2.  Computes validity flags `ok1` (square exists), `c` (non-negative T), `c1` (non-zero Y).

It proves:
1.  **Low-Level Correctness**: The flags correspond exactly to their mathematical definitions.
2.  **High-Level Correctness**: The function returns a result that matches `decompress_step2` **iff** the flags indicate success.

Namely:
    • The function always succeeds (no panic) for any valid field element `s`
    • ok1 is true if and only if the inverse square root of v · u2² exists
    • c is true if and only if t is negative
    • c1 is true if and only if y is zero
    • pt is a valid RistrettoPoint when ok1 = 1, c = 0, and c1 = 0
Moreover if the high-level function returns `some P`, then:
a) The Rust flags must be set to success (1, 0, 0)
b) The Rust point `pt` must match the mathematical point `P`
And conversely.
-/
theorem step_2_spec' (s : backend.serial.u64.field.FieldElement51)
    (h_s : ∀ i < 5, s[i]!.val < 2 ^ 52) :
    ∃ (ok1 c c1 : subtle.Choice) (pt : RistrettoPoint),
    step_2 s = ok (ok1, c, c1, pt) ∧

    (let s_val := s.toField
     let u1 := 1 - s_val ^ 2
     let u2 := 1 + s_val ^ 2
     let v := (-Ed25519.d) * u1 ^ 2 - u2 ^ 2

     (ok1.val = 1#u8 ↔ (v * u2 ^ 2 ≠ 0 ∧ IsSquare (v * u2 ^ 2))) ∧
     (c.val = 1#u8 ↔ math.is_negative pt.T.toField) ∧
     (c1.val = 1#u8 ↔ pt.Y.toField = 0)) ∧

    (∀ (P : Point Ed25519), ristretto.decompress_step2 s.toField = some P ↔
      (ok1.val = 1#u8 ∧ c.val = 0#u8 ∧ c1.val = 0#u8 ∧ pt.toPoint = P)) := by
  unfold step_2 field.FieldElement51.invsqrt subtle.ConditionallyNegatable.Blanket.conditional_negate
  progress
  · intro i hi; have := h_s i hi; omega
  rename_i ss ss_mod ss_bound
  progress as ⟨u1⟩
  · unfold backend.serial.u64.field.FieldElement51.ONE; try decide
  · intro i hi; have := ss_bound i hi; omega
  rename_i u1_bounds u1_post
  progress as ⟨ u2 , u2_post, u2_bounds ⟩
  · unfold backend.serial.u64.field.FieldElement51.ONE; try decide
  · intro i hi; have := ss_bound i hi; omega
  progress as ⟨ u3 , u3_post, u3_bounds ⟩
  progress as ⟨ u4 , u4_post, u4_bounds ⟩
  · unfold backend.serial.u64.constants.EDWARDS_D; try decide
  progress as ⟨u5, u5_post, u5_bounds⟩
  · intro i hi; have := u1_bounds i hi; omega
  progress as ⟨u6, u6_post, u6_bounds⟩
  · intro i hi; have := u4_bounds i hi; omega
  · intro i hi; have := u5_bounds i hi; omega
  progress as ⟨u7, u7_bounds, u7_post⟩
  · intro i hi; have := u6_bounds i hi; omega
  · intro i hi; have := u3_bounds i hi; omega
  progress as ⟨u8, u8_post, u8_bounds⟩
  · intro i hi; have := u7_bounds i hi; omega
  · intro i hi; have := u3_bounds i hi; omega
  progress as ⟨invsqrt_res, invsqrt_bounds, invsqrt_nonneg, invsqrt_post1, invsqrt_post2⟩
  · unfold backend.serial.u64.field.FieldElement51.ONE; try decide
  · intro i hi; have := u8_bounds i hi; omega
  progress as ⟨u10, u10_post, u10_bounds⟩
  · intro i hi; have := invsqrt_bounds i hi; omega
  progress as ⟨fe4, fe4_post, fe4_bounds⟩
  · intro i hi; have := u10_bounds i hi; omega
  · intro i hi; have := u7_bounds i hi; omega
  progress as ⟨Dy, Dy_post, Dy_bounds⟩
  · intro i hi; have := invsqrt_bounds i hi; omega
  · intro i hi; have := fe4_bounds i hi; omega
  progress as ⟨fe5, fe5_post, fe5_bounds⟩
  · intro i hi; have := h_s i hi; omega
  · intro i hi; have := h_s i hi; omega
  progress as ⟨x, x_post, x_bounds⟩
  · intro i hi; have := u10_bounds i hi; omega
  progress as ⟨x_neg, x_neg_post⟩
  progress as ⟨x_1, x_1_mod, x_1_bounds⟩
  · intro i hi; have := x_bounds i hi; omega
  progress as ⟨x1, x1_post⟩
  progress as ⟨y, y_post, y_bounds⟩
  · intro i hi; have := u1_bounds i hi; omega
  · intro i hi; have := Dy_bounds i hi; omega
  progress as ⟨t, t_post, t_bounds⟩
  · intro i hi
    rw [x1_post i hi]
    split
    · have := x_1_bounds i hi; omega
    · have := x_bounds i hi; omega
  · intro i hi; have := y_bounds i hi; omega
  progress as ⟨c, c_post⟩
  progress as ⟨c1, c1_post⟩
  -- Shared setup for Goals 1 and 4
  have h_one : Field51_as_Nat FieldElement51.ONE % p = 1 := by
    simp [FieldElement51.ONE_spec]; decide
  rename_i invsqrt_case3 invsqrt_case4
  simp only [h_one, ne_eq, one_ne_zero, not_false_eq_true, true_and,
    mul_one] at invsqrt_post1 invsqrt_post2 invsqrt_case3 invsqrt_case4
  -- Shared bridges for Goals 1 and 4
  set W := (-Ed25519.d * (1 - s.toField ^ 2) ^ 2 - (1 + s.toField ^ 2) ^ 2) *
           (1 + s.toField ^ 2) ^ 2 with hW_def
  have h_u8_field : u8.toField = W := by
    -- Lift each Nat-level hypothesis to a CurveField equality
    have hss : ss.toField = s.toField ^ 2 := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ ss_mod; push_cast at this; exact this
    have hu1_add : u1.toField + ss.toField = 1 := by
      unfold FieldElement51.toField
      have := lift_mod_eq _ _ u1_post; push_cast at this
      simpa [FieldElement51.ONE_spec] using this
    have hu2_nat : Field51_as_Nat u2 = Field51_as_Nat FieldElement51.ONE + Field51_as_Nat ss := by
      unfold Field51_as_Nat
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi; rw [Finset.mem_range] at hi; rw [u2_post i hi, mul_add]
    have hu2 : u2.toField = 1 + ss.toField := by
      unfold FieldElement51.toField; rw [hu2_nat]; push_cast; simp [FieldElement51.ONE_spec]
    have hu3 : u3.toField = u2.toField ^ 2 := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ u3_post; push_cast at this; exact this
    have hd : (backend.serial.u64.constants.EDWARDS_D).toField = Ed25519.d := by
      unfold FieldElement51.toField; rw [backend.serial.u64.constants.EDWARDS_D_spec]; rfl
    have hu4_add : (backend.serial.u64.constants.EDWARDS_D).toField + u4.toField = 0 := by
      unfold FieldElement51.toField
      have := lift_mod_eq _ _ (show (Field51_as_Nat backend.serial.u64.constants.EDWARDS_D +
        Field51_as_Nat u4) % p = 0 % p by simp [u4_post])
      push_cast at this; exact this
    have hu5 : u5.toField = u1.toField ^ 2 := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ u5_post; push_cast at this; exact this
    have hu6 : u6.toField = u4.toField * u5.toField := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ u6_post; push_cast at this; exact this
    have hu7_add : u7.toField + u3.toField = u6.toField := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ u7_post; push_cast at this; exact this
    have hu8 : u8.toField = u7.toField * u3.toField := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ u8_post; push_cast at this; exact this
    -- Derive intermediate equalities
    have hu1 : u1.toField = 1 - ss.toField := by linear_combination hu1_add
    have hu4 : u4.toField = -Ed25519.d := by linear_combination hu4_add - hd
    have hu7 : u7.toField = u6.toField - u3.toField := by linear_combination hu7_add
    -- Chain rewrites to express u8.toField in terms of s.toField and Ed25519.d
    rw [hu8, hu7, hu6, hu4, hu5, hu3, hu2, hu1, hss]
  -- Bridge: u8 % p ≠ 0 ↔ W ≠ 0
  have h_ne_bridge : Field51_as_Nat u8 % p ≠ 0 ↔ W ≠ 0 := by
    rw [← h_u8_field, FieldElement51.toField]
    simp only [ne_eq, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  -- Bridge: Nat-level ∃ x ↔ u8%p ≠ 0 ∧ IsSquare W
  have h_sq_bridge : (∃ x : Nat, (x ^ 2 * (Field51_as_Nat u8 % p)) % p = 1) ↔
      (Field51_as_Nat u8 % p ≠ 0 ∧ IsSquare W) := by
    set w := Field51_as_Nat u8 % p with hw_def
    have h_w_eq : (w : CurveField) = W := by
      rw [← h_u8_field, FieldElement51.toField, hw_def, ZMod.natCast_mod]
    have h_1mod : (1 : ℕ) % p = 1 := by decide
    constructor
    · -- → : n²·w ≡ 1 (mod p) → w ≠ 0 ∧ IsSquare W
      rintro ⟨n, hn⟩
      have h_nz : w ≠ 0 := by intro h_zero; simp [h_zero] at hn
      have h_zmod : (n : CurveField) ^ 2 * W = 1 := by
        rw [← h_w_eq]
        have := lift_mod_eq _ _ (show (n ^ 2 * w) % p = 1 % p by rw [h_1mod]; exact hn)
        push_cast at this; exact this
      have hn_ne : (n : CurveField) ≠ 0 := by intro h; simp [h] at h_zmod
      refine ⟨h_nz, ⟨(n : CurveField)⁻¹, ?_⟩⟩
      -- W = ((↑n)²)⁻¹ = (↑n⁻¹)² = ↑n⁻¹ · ↑n⁻¹
      suffices h : W = ((n : CurveField) ^ 2)⁻¹ by rw [← inv_pow, sq] at h; exact h
      exact mul_left_cancel₀ (pow_ne_zero 2 hn_ne)
        (h_zmod.trans (mul_inv_cancel₀ (pow_ne_zero 2 hn_ne)).symm)
    · -- ← : w ≠ 0 ∧ IsSquare W → ∃ n, n²·w ≡ 1 (mod p)
      rintro ⟨h_nz, r, hr⟩
      have hr_ne : r ≠ 0 := by
        intro h; rw [h, zero_mul] at hr; exact (h_ne_bridge.mp h_nz) hr
      use r⁻¹.val
      have h_zmod : r⁻¹ ^ 2 * W = 1 := by rw [hr]; field_simp
      rw [← h_w_eq] at h_zmod
      rw [← h_1mod]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
        push_cast [ZMod.val_natCast] at h_zmod ⊢; simp only [ZMod.natCast_val, ZMod.cast_id',
          id_eq]; grind only [cases eager Prod])
  refine ⟨invsqrt_res.1, c, c1,
    ⟨x1, y, backend.serial.u64.field.FieldElement51.ONE, t⟩,
    rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- Goal 1: ok1 ↔ (v * u2² ≠ 0 ∧ IsSquare(v * u2²))
    constructor
    · intro h_ok
      have h_nz : Field51_as_Nat u8 % p ≠ 0 := by
        intro h_zero; exact absurd h_ok (by rw [(invsqrt_post2 h_zero).1]; decide)
      have h_ex : ∃ x : Nat, (x ^ 2 * (Field51_as_Nat u8 % p)) % p = 1 := by
        by_contra h_nex
        exact absurd h_ok (by rw [(invsqrt_case4 ⟨h_nz, h_nex⟩).1]; decide)
      exact ⟨h_ne_bridge.mp h_nz, (h_sq_bridge.mp h_ex).2⟩
    · -- ← direction
      intro ⟨h_ne, h_sq⟩
      have h_nz : Field51_as_Nat u8 % p ≠ 0 := h_ne_bridge.mpr h_ne
      exact (invsqrt_case3 ⟨h_nz, h_sq_bridge.mpr ⟨h_nz, h_sq⟩⟩).1
  · -- Goal 2: c ↔ math.is_negative t.toField
    simp only [c_post, math.is_negative, FieldElement51.toField, ZMod.val_natCast, beq_iff_eq]
  · -- Goal 3: c1 ↔ y.toField = 0
    simp only [c1_post, FieldElement51.toField, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  · -- Goal 4: ∀ P, decompress_step2 ... ↔ ...
    intro P
    -- Field bridges for remaining intermediate variables
    have hu10 : u10.toField = invsqrt_res.2.toField * u2.toField := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ u10_post; push_cast at this; exact this
    have hfe4 : fe4.toField = u10.toField * u7.toField := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ fe4_post; push_cast at this; exact this
    have hDy_field : Dy.toField = invsqrt_res.2.toField * fe4.toField := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ Dy_post; push_cast at this; exact this
    have hfe5_nat : Field51_as_Nat fe5 = Field51_as_Nat s + Field51_as_Nat s := by
      unfold Field51_as_Nat
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi; rw [Finset.mem_range] at hi; rw [fe5_post i hi, mul_add]
    have hfe5 : fe5.toField = 2 * s.toField := by
      unfold FieldElement51.toField; rw [hfe5_nat]; push_cast; ring
    have hx_field : x.toField = fe5.toField * u10.toField := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ x_post; push_cast at this; exact this
    have hy_field : y.toField = u1.toField * Dy.toField := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ y_post; push_cast at this; exact this
    have ht_field : t.toField = x1.toField * y.toField := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ t_post; push_cast at this; exact this
    -- x_1 is the negation of x in the field
    have hx_1_neg : x_1.toField = -x.toField := by
      unfold FieldElement51.toField
      have h := lift_mod_eq _ _ (show (Field51_as_Nat x + Field51_as_Nat x_1) % p = 0 % p by simp [x_1_mod])
      push_cast at h; grind only [cases eager Prod]

    -- x1 = conditional select at Nat level
    have hx1_nat : Field51_as_Nat x1 = if x_neg.val = 1#u8 then Field51_as_Nat x_1 else Field51_as_Nat x := by
      unfold Field51_as_Nat
      split <;> rename_i h
      · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
        have := x1_post i hi; rw [if_pos h] at this; exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
      · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
        have := x1_post i hi; rw [if_neg h] at this; exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
    -- x1 = conditional select at field level
    have hx1_select : x1.toField = if x_neg.val = 1#u8 then x_1.toField else x.toField := by
      unfold FieldElement51.toField; rw [hx1_nat]; split <;> rfl
    -- x1 = abs_edwards(x)
    have hx1_abs : x1.toField = math.abs_edwards x.toField := by
      rw [hx1_select, hx_1_neg, math.abs_edwards, math.is_negative]
      by_cases hxn : x_neg.val = 1#u8
      · rw [if_pos hxn]
        have : (x.toField.val % 2 == 1) = true := by
          rw [beq_iff_eq]; unfold FieldElement51.toField; rw [ZMod.val_natCast]
          exact x_neg_post.mp hxn
        simp [this]
      · rw [if_neg hxn]
        have : (x.toField.val % 2 == 1) = false := by
          rw [Bool.eq_false_iff]; intro h; rw [beq_iff_eq] at h
          exact hxn (x_neg_post.mpr (by unfold FieldElement51.toField at h; rwa [ZMod.val_natCast] at h))
        simp [this]
    -- When ok1=1: I²·W = 1 in CurveField
    have hI_sq_W : invsqrt_res.1.val = 1#u8 → invsqrt_res.2.toField ^ 2 * W = 1 := by
      intro h_ok1
      have h_nz : Field51_as_Nat u8 % p ≠ 0 := by
        intro h_zero; exact absurd h_ok1 (by rw [(invsqrt_post2 h_zero).1]; decide)
      have h_ex : ∃ z : Nat, (z ^ 2 * (Field51_as_Nat u8 % p)) % p = 1 := by
        by_contra h_nex; exact absurd h_ok1 (by rw [(invsqrt_case4 ⟨h_nz, h_nex⟩).1]; decide)
      have h_sq := (invsqrt_case3 ⟨h_nz, h_ex⟩).2
      rw [← h_u8_field]; unfold FieldElement51.toField
      have h := lift_mod_eq ((Field51_as_Nat invsqrt_res.2 % p) ^ 2 * (Field51_as_Nat u8 % p)) 1
        (by rw [show (1 : Nat) % p = 1 from by decide]; exact h_sq)
      push_cast at h; simp only [ZMod.natCast_mod] at h; exact h
    -- Re-derive standalone field-level values for u1, u2 (needed for decompress_step2 matching)
    have hss_field : ss.toField = s.toField ^ 2 := by
      unfold FieldElement51.toField; have := lift_mod_eq _ _ ss_mod; push_cast at this; exact this
    have hu1_val : u1.toField = 1 - s.toField ^ 2 := by
      have : u1.toField + ss.toField = 1 := by
        unfold FieldElement51.toField; have := lift_mod_eq _ _ u1_post; push_cast at this
        simpa [FieldElement51.ONE_spec] using this
      rw [hss_field] at this
      linear_combination this
    have hu2_val : u2.toField = 1 + s.toField ^ 2 := by
      have : Field51_as_Nat u2 = Field51_as_Nat FieldElement51.ONE + Field51_as_Nat ss := by
        unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi; rw [u2_post i hi, mul_add]
      unfold FieldElement51.toField; rw [this]; push_cast
      rw [FieldElement51.ONE_spec]; push_cast
      have hss := hss_field; unfold FieldElement51.toField at hss; rw [hss]

    -- Re-derive u7.toField (= v in the math) in terms of d, u1, u2
    have hu7_val : u7.toField = (-Ed25519.d) * u1.toField ^ 2 - u2.toField ^ 2 := by
      have hu3 : u3.toField = u2.toField ^ 2 := by
        unfold FieldElement51.toField; have := lift_mod_eq _ _ u3_post; push_cast at this; exact this
      have hd : (backend.serial.u64.constants.EDWARDS_D).toField = Ed25519.d := by
        unfold FieldElement51.toField; rw [backend.serial.u64.constants.EDWARDS_D_spec]; rfl
      have hu4 : u4.toField = -Ed25519.d := by
        have : (backend.serial.u64.constants.EDWARDS_D).toField + u4.toField = 0 := by
          unfold FieldElement51.toField
          have := lift_mod_eq _ _ (show (Field51_as_Nat backend.serial.u64.constants.EDWARDS_D +
            Field51_as_Nat u4) % p = 0 % p by simp [u4_post])
          push_cast at this; exact this
        linear_combination this - hd
      have hu5 : u5.toField = u1.toField ^ 2 := by
        unfold FieldElement51.toField; have := lift_mod_eq _ _ u5_post; push_cast at this; exact this
      have hu6 : u6.toField = u4.toField * u5.toField := by
        unfold FieldElement51.toField; have := lift_mod_eq _ _ u6_post; push_cast at this; exact this
      have hu7_add : u7.toField + u3.toField = u6.toField := by
        unfold FieldElement51.toField; have := lift_mod_eq _ _ u7_post; push_cast at this; exact this
      rw [hu4, hu5] at hu6; rw [hu3, hu6] at hu7_add
      linear_combination hu7_add
    -- W = v * u2^2 at field level
    have hW_eq : W = u7.toField * u2.toField ^ 2 := by
      rw [hW_def, hu2_val, hu7_val, hu1_val];
      simp only [neg_mul, mul_eq_mul_right_iff, sub_right_inj, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff]
      left; rw [hu2_val]
    constructor
    · -- → direction: decompress_step2 s.toField = some P → ok1=1 ∧ c=0 ∧ c1=0 ∧ pt.toPoint = P
      intro h_decomp
      -- Use forward helper (sorry'd) to get data in Ed25519.d form
      have h_fwd := decompress_step2_forward s.toField P h_decomp
        u1.toField u2.toField u7.toField W hu1_val hu2_val hu7_val hW_eq
      obtain ⟨h_sq, h_W_ne, h_neg_fwd, h_y_ne_fwd, h_coords⟩ := h_fwd
      -- Step 1: ok1 = 1 (from IsSquare W ∧ W ≠ 0)
      have h_ok1 : invsqrt_res.1.val = 1#u8 := by
        have h_nz := h_ne_bridge.mpr h_W_ne
        have h_ex := h_sq_bridge.mpr ⟨h_nz, h_sq⟩
        exact (invsqrt_case3 ⟨h_nz, h_ex⟩).1
      -- Step 2: Get I_rust² * W = 1
      have hI := hI_sq_W h_ok1
      -- Step 3: Get coordinate equalities from h_coords
      have ⟨h_Px, h_Py⟩ := h_coords invsqrt_res.2.toField hI
      -- Re-derive simplified coordinate forms (needed for bridging)
      have hx_simp : x.toField = 2 * s.toField * invsqrt_res.2.toField * u2.toField := by
        rw [hx_field, hfe5, hu10]; ring
      have hy_simp : y.toField = u1.toField * (invsqrt_res.2.toField ^ 2 * u2.toField * u7.toField) := by
        rw [hy_field, hDy_field, hfe4, hu10]; ring
      -- Step 4: Bridge Rust intermediates to P's coordinates
      have hx1_eq_Px : x1.toField = P.x := by rw [hx1_abs, hx_simp]; exact h_Px.symm
      have hy_eq_Py : y.toField = P.y := by rw [hy_simp]; exact h_Py.symm
      -- Step 5: c = 0 (is_negative (P.x * P.y) = false → t not negative → c ≠ 1)
      have h_c : c.val = 0#u8 := by
        rcases c.valid with h | h
        · exact h
        · exfalso
          have h_t_neg : Field51_as_Nat t % p % 2 = 1 := c_post.mp h
          have h_t_field : P.x * P.y = t.toField := by
            rw [← hx1_eq_Px, ← hy_eq_Py, ht_field]
          have : is_negative t.toField = false := h_t_field ▸ h_neg_fwd
          simp only [is_negative, FieldElement51.toField, ZMod.val_natCast,
            beq_eq_false_iff_ne] at this
          exact this h_t_neg
      -- Step 6: c1 = 0 (P.y ≠ 0 → y not zero → c1 ≠ 1)
      have h_c1 : c1.val = 0#u8 := by
        rcases c1.valid with h | h
        · exact h
        · exfalso
          have h_y_zero : Field51_as_Nat y % p = 0 := c1_post.mp h
          have : y.toField = 0 := by
            simp only [FieldElement51.toField, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
            exact h_y_zero
          rw [hy_eq_Py] at this
          exact h_y_ne_fwd this
      -- Step 7: toPoint = P (coordinates match + Z = 1)
      have hONE : FieldElement51.ONE.toField = (1 : CurveField) := by
        unfold FieldElement51.toField; rw [FieldElement51.ONE_spec]; simp
      have h_valid : edwards.EdwardsPoint.IsValid
          { X := x1, Y := y, Z := FieldElement51.ONE, T := t } := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- X_bounds
          change ∀ i < 5, x1[i]!.val < 2 ^ 53
          intro i hi; rw [x1_post i hi]; split
          · have := x_1_bounds i hi; omega
          · have := x_bounds i hi; omega
        · -- Y_bounds
          change ∀ i < 5, y[i]!.val < 2 ^ 53
          intro i hi; have := y_bounds i hi; omega
        · -- Z_bounds
          change ∀ i < 5, FieldElement51.ONE[i]!.val < 2 ^ 53
          intro i hi; unfold FieldElement51.ONE; interval_cases i <;> decide
        · -- T_bounds
          change ∀ i < 5, t[i]!.val < 2 ^ 53
          intro i hi; have := t_bounds i hi; omega
        · -- Z_ne_zero
          change FieldElement51.ONE.toField ≠ 0
          rw [hONE]; exact one_ne_zero
        · -- T_relation
          change x1.toField * y.toField = t.toField * FieldElement51.ONE.toField
          rw [ht_field, hONE, mul_one]
        · -- on_curve
          dsimp only
          simp only [hONE, one_pow, mul_one]
          have h_x1_sq : x1.toField ^ 2 = x.toField ^ 2 := by
            rw [hx1_abs]; exact abs_edwards_sq x.toField
          rw [h_x1_sq, hx_simp, hy_simp]
          have hIW : invsqrt_res.2.toField ^ 2 * (u7.toField * u2.toField ^ 2) = 1 := by
            rw [← hW_eq]; exact hI
          exact on_curve_from_decompression Ed25519.a Ed25519.d s.toField
            invsqrt_res.2.toField u1.toField u2.toField u7.toField
            (by simp [Ed25519]) hu1_val hu2_val hu7_val hIW
      have hPt := edwards.EdwardsPoint.toPoint_of_isValid h_valid
      refine ⟨h_ok1, h_c, h_c1, ?_⟩
      ext
      · -- x coordinate
        simp only [RistrettoPoint.toPoint, hPt.1, hONE, div_one, hx1_eq_Px]
      · -- y coordinate
        simp only [RistrettoPoint.toPoint, hPt.2, hONE, div_one, hy_eq_Py]
    · -- ← direction: ok1=1 ∧ c=0 ∧ c1=0 ∧ pt.toPoint = P → decompress_step2 s.toField = some P
      intro ⟨h_ok1, h_c, h_c1, h_pt⟩
      -- Derive key facts from ok1=1
      have h_nz : Field51_as_Nat u8 % p ≠ 0 := by
        intro h_zero; exact absurd h_ok1 (by rw [(invsqrt_post2 h_zero).1]; decide)
      have h_ex : ∃ z : Nat, (z ^ 2 * (Field51_as_Nat u8 % p)) % p = 1 := by
        by_contra h_nex
        exact absurd h_ok1 (by rw [(invsqrt_case4 ⟨h_nz, h_nex⟩).1]; decide)
      have hIsSquare_W : IsSquare W := (h_sq_bridge.mp h_ex).2
      have hW_ne : W ≠ 0 := h_ne_bridge.mp h_nz
      have hI_sq := hI_sq_W h_ok1  -- I_rust^2 * W = 1
      have hI_sq_inv : invsqrt_res.2.toField ^ 2 = W⁻¹ :=
        eq_inv_of_mul_eq_one_left hI_sq
      -- Coordinate simplifications: express Rust intermediates in terms of I², u1, u2, u7
      have hDy_simp : Dy.toField = invsqrt_res.2.toField ^ 2 * u2.toField * u7.toField := by
        rw [hDy_field, hfe4, hu10]; ring
      have hy_simp : y.toField = u1.toField * (invsqrt_res.2.toField ^ 2 * u2.toField * u7.toField) := by
        rw [hy_field, hDy_simp]
      have hx_simp : x.toField = 2 * s.toField * invsqrt_res.2.toField * u2.toField := by
        rw [hx_field, hfe5, hu10]; ring
      -- Step A: ONE.toField = 1
      have hONE : FieldElement51.ONE.toField = (1 : CurveField) := by
        unfold FieldElement51.toField; rw [FieldElement51.ONE_spec]; simp
      -- Step B: Prove EdwardsPoint validity
      have h_valid : edwards.EdwardsPoint.IsValid
          { X := x1, Y := y, Z := FieldElement51.ONE, T := t } := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- X_bounds
          change ∀ i < 5, x1[i]!.val < 2 ^ 53
          intro i hi; rw [x1_post i hi]; split
          · have := x_1_bounds i hi; omega
          · have := x_bounds i hi; omega
        · -- Y_bounds
          change ∀ i < 5, y[i]!.val < 2 ^ 53
          intro i hi; have := y_bounds i hi; omega
        · -- Z_bounds
          change ∀ i < 5, FieldElement51.ONE[i]!.val < 2 ^ 53
          intro i hi; unfold FieldElement51.ONE; interval_cases i <;> decide
        · -- T_bounds
          change ∀ i < 5, t[i]!.val < 2 ^ 53
          intro i hi; have := t_bounds i hi; omega
        · -- Z_ne_zero
          change FieldElement51.ONE.toField ≠ 0
          rw [hONE]; exact one_ne_zero
        · -- T_relation
          change x1.toField * y.toField = t.toField * FieldElement51.ONE.toField
          rw [ht_field, hONE, mul_one]
        · -- on_curve (curve equation via decompress_helper)
          dsimp only
          simp only [hONE, one_pow, mul_one]
          have h_x1_sq : x1.toField ^ 2 = x.toField ^ 2 := by
            rw [hx1_abs]; exact abs_edwards_sq x.toField
          rw [h_x1_sq, hx_simp, hy_simp]
          have hIW : invsqrt_res.2.toField ^ 2 * (u7.toField * u2.toField ^ 2) = 1 := by
            rw [← hW_eq]; exact hI_sq
          exact on_curve_from_decompression Ed25519.a Ed25519.d s.toField
            invsqrt_res.2.toField u1.toField u2.toField u7.toField
            (by simp [Ed25519]) hu1_val hu2_val hu7_val hIW
      -- Step C: Extract P.x and P.y from h_pt
      have ⟨hPx, hPy⟩ := toPoint_coords h_valid hONE h_pt
      -- Step D: is_negative (P.x * P.y) = false (from c = 0)
      have h_neg := is_negative_Pxy_false hPx hPy ht_field h_c c_post
      -- Step E: P.y ≠ 0 (from c1 = 0)
      have h_y_ne := Py_ne_zero hPy h_c1 c1_post
      -- Step F: Apply decompress_step2_backward
      have hIW : invsqrt_res.2.toField ^ 2 * (u7.toField * u2.toField ^ 2) = 1 := by
        rw [← hW_eq]; exact hI_sq
      exact decompress_step2_backward s.toField invsqrt_res.2.toField
        u1.toField u2.toField u7.toField hu1_val hu2_val hu7_val hIW P
        h_neg h_y_ne
        (by rw [hPx, hx1_abs, hx_simp])
        (by rw [hPy, hy_simp])

@[progress]
theorem step_2_spec (s : backend.serial.u64.field.FieldElement51)
    (h_s : ∀ i < 5, s[i]!.val < 2 ^ 52) :
    step_2 s ⦃ (ok1, c, c1, pt) =>
    (let s_val := s.toField
     let u1 := 1 - s_val ^ 2
     let u2 := 1 + s_val ^ 2
     let v := (-Ed25519.d) * u1 ^ 2 - u2 ^ 2
     (ok1.val = 1#u8 ↔ (v * u2 ^ 2 ≠ 0 ∧ IsSquare (v * u2 ^ 2))) ∧
     (c.val = 1#u8 ↔ math.is_negative pt.T.toField) ∧
     (c1.val = 1#u8 ↔ pt.Y.toField = 0)) ∧
    (∀ (P : Point Ed25519), ristretto.decompress_step2 s.toField = some P ↔
      (ok1.val = 1#u8 ∧ c.val = 0#u8 ∧ c1.val = 0#u8 ∧ pt.toPoint = P)) ⦄ := by
  obtain ⟨ok1, c, c1, pt, h_ok, h_post⟩ := step_2_spec' s h_s
  exact exists_imp_spec ⟨(ok1, c, c1, pt), h_ok, h_post⟩

end curve25519_dalek.ristretto.decompress
