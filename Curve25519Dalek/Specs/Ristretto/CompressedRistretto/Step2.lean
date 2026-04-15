/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
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
import Curve25519Dalek.Specs.Field.FieldElement51.InvSqrt
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Field.FieldElement51.IsZero
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EdwardsD
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE

/-!
# Spec theorem for `curve25519_dalek::ristretto::decompress::step_2`

Takes a field element `s` as input (from step_1) and performs the second step of Ristretto
decompression, computing the coordinates of an Edwards curve point via the inverse Ristretto
encoding map. Concretely:

- Computes `ss = s^2`, `u1 = 1 - ss`, `u2 = 1 + ss`, `u2_sqr = u2^2`
- Computes `v = (-EDWARDS_D) * u1^2 - u2^2` and `W = v * u2^2`
- Computes `(ok1, I) = invsqrt(W)`, where `ok1` indicates whether the inverse square root exists
- Derives `Dx = I * u2`, `Dy = I * Dx * v`, `x = 2 * s * Dx`; conditionally negates `x` if
  negative, producing `x1`; then `y = u1 * Dy` and `t = x1 * y`
- Returns `(ok1, c, c1, pt)` where `c` flags whether `t` is negative, `c1` flags whether
  `y = 0`, and `pt = { X := x1, Y := y, Z := 1, T := t }` in extended twisted Edwards form

The three `Choice` flags `(ok1, c, c1)` are consumed by the full `decompress` function to
validate the decompression result.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards
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
    constructor
    · -- P.x = abs_edwards (2 * s * I * u2)
      rw [h_Px']
      -- Prove squares are equal via separate ring lemmas (avoids ring_nf unfolding I_math)
      have h_x_sq : (2 * s * I * u2) ^ 2 = (2 * s * (I_math * u2)) ^ 2 := by
        have h1 : (2 * s * I * u2) ^ 2 = 4 * s ^ 2 * I ^ 2 * u2 ^ 2 := by ring
        have h2 : (2 * s * (I_math * u2)) ^ 2 = 4 * s ^ 2 * I_math ^ 2 * u2 ^ 2 := by ring
        rw [h1, h2, hI_sq_eq]
      exact (abs_edwards_eq_of_sq_eq h_x_sq).symm
    · -- P.y = u1 * (I^2 * u2 * v)
      rw [h_Py']
      -- Rewrite I_math * (I_math * u2) * v to I_math^2 * u2 * v, then to I^2 * u2 * v
      have h1 : I_math * (I_math * u2) * v = I_math ^ 2 * u2 * v := by ring
      rw [h1, ← hI_sq_eq]

set_option maxHeartbeats 400000 in -- increased for step* through many sub-calls
/-- **Spec theorem for `curve25519_dalek::ristretto::decompress::step_2`**
• The function always succeeds (no panic) for any valid field element `s`
• `ok1.val = 1` iff `v * u2^2 ≠ 0 ∧ IsSquare(v * u2^2)`, where `u1 = 1 - s^2`,
  `u2 = 1 + s^2`, `v = (-EDWARDS_D) * u1^2 - u2^2`
• `c.val = 1` iff `pt.T` is negative (i.e. `pt.T.toField` has odd canonical representative)
• `c1.val = 1` iff `pt.Y.toField = 0`
• `decompress_step2 s.toField = some P` iff `ok1 = 1 ∧ c = 0 ∧ c1 = 0 ∧ pt.toPoint = P`
• When `ok1 = 1 ∧ c = 0 ∧ c1 = 0`, `pt` is a valid `RistrettoPoint`
-/
@[step]
theorem step_2_spec (s : backend.serial.u64.field.FieldElement51)
    (h_s : ∀ i < 5, s[i]!.val < 2 ^ 52) :
    step_2 s ⦃ ((ok1, c, c1, pt) :
        subtle.Choice × subtle.Choice × subtle.Choice × RistrettoPoint) =>
      (let s_val := s.toField
       let u1 := 1 - s_val ^ 2
       let u2 := 1 + s_val ^ 2
       let v := (-Ed25519.d) * u1 ^ 2 - u2 ^ 2
       (ok1.val = 1#u8 ↔ (v * u2 ^ 2 ≠ 0 ∧ IsSquare (v * u2 ^ 2))) ∧
       (c.val = 1#u8 ↔ math.is_negative pt.T.toField) ∧
       (c1.val = 1#u8 ↔ pt.Y.toField = 0)) ∧
      (∀ (P : Point Ed25519), ristretto.decompress_step2 s.toField = some P ↔
        (ok1.val = 1#u8 ∧ c.val = 0#u8 ∧ c1.val = 0#u8 ∧ pt.toPoint = P)) ∧
      (ok1.val = 1#u8 ∧ c.val = 0#u8 ∧ c1.val = 0#u8 → RistrettoPoint.IsValid pt) ⦄ := by
  unfold step_2
  step*
  rename_i invsqrt _ invsqrt_bounds invsqrt_nonneg invsqrt_case1 invsqrt_case2 invsqrt_case3
    _ _ _ _ _ _ _ _ _ _ _
  -- Shared setup: ONE field value
  have hONE : one.toField = (1 : CurveField) := by
    unfold FieldElement51.toField; rw [one_post1]; simp
  -- Field bridges: lift Nat-level mod equalities to CurveField
  have hss : ss.toField = s.toField ^ 2 := by
    unfold FieldElement51.toField; have := lift_mod_eq _ _ ss_post1; push_cast at this; exact this
  have hu1_add : u1.toField + ss.toField = one.toField := by
    unfold FieldElement51.toField; have := lift_mod_eq _ _ u1_post2; push_cast at this; exact this
  have hu1_val : u1.toField = 1 - s.toField ^ 2 := by
    rw [hONE] at hu1_add; rw [hss] at hu1_add; linear_combination hu1_add
  have hu2_nat : Field51_as_Nat u2 = Field51_as_Nat one + Field51_as_Nat ss := by
    unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi; rw [u2_post1 i hi, mul_add]
  have hu2_val : u2.toField = 1 + s.toField ^ 2 := by
    unfold FieldElement51.toField; rw [hu2_nat]; push_cast
    rw [one_post1]; push_cast
    have hss' := hss; unfold FieldElement51.toField at hss'; rw [hss']
  have hu2_sqr : u2_sqr.toField = u2.toField ^ 2 := by
    unfold FieldElement51.toField
    have := lift_mod_eq _ _ u2_sqr_post1; push_cast at this; exact this
  have hfe_d : fe.toField = Ed25519.d := by
    unfold FieldElement51.toField; rw [fe_post1]; rfl
  have hfe_neg_add : fe.toField + neg_d.toField = 0 := by
    unfold FieldElement51.toField
    have := lift_mod_eq _ _ (show (Field51_as_Nat fe + Field51_as_Nat neg_d) % p = 0 % p by
      rw [Nat.zero_mod]; exact neg_d_post1)
    push_cast at this; exact this
  have hneg_d : neg_d.toField = -Ed25519.d := by
    linear_combination hfe_neg_add - hfe_d
  have hu1_sq : u1_sq.toField = u1.toField ^ 2 := by
    unfold FieldElement51.toField
    have := lift_mod_eq _ _ u1_sq_post1; push_cast at this; exact this
  have hneg_d_u1_sq : neg_d_u1_sq.toField = neg_d.toField * u1_sq.toField := by
    unfold FieldElement51.toField
    have := lift_mod_eq _ _ neg_d_u1_sq_post1; push_cast at this; exact this
  have hv_add : v.toField + u2_sqr.toField = neg_d_u1_sq.toField := by
    unfold FieldElement51.toField; have := lift_mod_eq _ _ v_post2; push_cast at this; exact this
  have hv_val : v.toField = (-Ed25519.d) * u1.toField ^ 2 - u2.toField ^ 2 := by
    rw [hneg_d, hu1_sq] at hneg_d_u1_sq; rw [hu2_sqr, hneg_d_u1_sq] at hv_add
    linear_combination hv_add
  have hv_u2_sqr : v_u2_sqr.toField = v.toField * u2_sqr.toField := by
    unfold FieldElement51.toField
    have := lift_mod_eq _ _ v_u2_sqr_post1; push_cast at this; exact this
  -- Set W = the combined expression
  set W := (-Ed25519.d * (1 - s.toField ^ 2) ^ 2 - (1 + s.toField ^ 2) ^ 2) *
           (1 + s.toField ^ 2) ^ 2 with hW_def
  have h_v_u2_sqr_field : v_u2_sqr.toField = W := by
    rw [hv_u2_sqr, hu2_sqr, hv_val, hu2_val, hW_def, hu1_val]
  have hW_eq : W = v.toField * u2.toField ^ 2 := by
    rw [hW_def, hu2_val, hv_val, hu1_val]
    simp only [neg_mul, mul_eq_mul_right_iff, sub_right_inj, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff]
    left; rw [hu2_val]
  -- Bridge: v_u2_sqr % p ≠ 0 ↔ W ≠ 0
  have h_ne_bridge : Field51_as_Nat v_u2_sqr % p ≠ 0 ↔ W ≠ 0 := by
    rw [← h_v_u2_sqr_field, FieldElement51.toField]
    simp only [ne_eq, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  -- Bridge: Nat-level ∃ x ↔ v_u2_sqr%p ≠ 0 ∧ IsSquare W
  have h_sq_bridge : (∃ x : Nat, (x ^ 2 * (Field51_as_Nat v_u2_sqr % p)) % p = 1) ↔
      (Field51_as_Nat v_u2_sqr % p ≠ 0 ∧ IsSquare W) := by
    set w := Field51_as_Nat v_u2_sqr % p with hw_def
    have h_w_eq : (w : CurveField) = W := by
      rw [← h_v_u2_sqr_field, FieldElement51.toField, hw_def, ZMod.natCast_mod]
    have h_1mod : (1 : ℕ) % p = 1 := by decide
    constructor
    · -- → : n²·w ≡ 1 (mod p) → w ≠ 0 ∧ IsSquare W
      rintro ⟨n, hn⟩
      have h_nz : w ≠ 0 := by intro h_zero; simp only [h_zero, mul_zero, Nat.zero_mod,
        zero_ne_one] at hn
      have h_zmod : (n : CurveField) ^ 2 * W = 1 := by
        rw [← h_w_eq]
        have := lift_mod_eq _ _ (show (n ^ 2 * w) % p = 1 % p by rw [h_1mod]; exact hn)
        push_cast at this; exact this
      have hn_ne : (n : CurveField) ≠ 0 := by intro h; simp only [h, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, zero_ne_one] at h_zmod
      refine ⟨h_nz, ⟨(n : CurveField)⁻¹, ?_⟩⟩
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
  -- Shared field bridges for coordinate expressions
  have hDx : Dx.toField = invsqrt.2.toField * u2.toField := by
    unfold FieldElement51.toField; have := lift_mod_eq _ _ Dx_post1; push_cast at this; exact this
  have hDx_v : Dx_v.toField = Dx.toField * v.toField := by
    unfold FieldElement51.toField; have := lift_mod_eq _ _ Dx_v_post1; push_cast at this; exact this
  have hDy_field : Dy.toField = invsqrt.2.toField * Dx_v.toField := by
    unfold FieldElement51.toField; have := lift_mod_eq _ _ Dy_post1; push_cast at this; exact this
  have hs_plus_s_nat : Field51_as_Nat s_plus_s = Field51_as_Nat s + Field51_as_Nat s := by
    unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi; rw [s_plus_s_post1 i hi, mul_add]
  have hs_plus_s : s_plus_s.toField = 2 * s.toField := by
    unfold FieldElement51.toField; rw [hs_plus_s_nat]; push_cast; ring
  have hx_field : x.toField = s_plus_s.toField * Dx.toField := by
    unfold FieldElement51.toField; have := lift_mod_eq _ _ x_post1; push_cast at this; exact this
  have hy_field : y.toField = u1.toField * Dy.toField := by
    unfold FieldElement51.toField; have := lift_mod_eq _ _ y_post1; push_cast at this; exact this
  have ht_field : t.toField = x1.toField * y.toField := by
    unfold FieldElement51.toField; have := lift_mod_eq _ _ t_post1; push_cast at this; exact this
  have hx_negated_neg : x_negated.toField = -x.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ (show (Field51_as_Nat x + Field51_as_Nat x_negated) % p = 0 % p by
      rw [Nat.zero_mod]; exact x_negated_post1)
    push_cast at h; grind
  have hx1_nat : Field51_as_Nat x1 =
      if x_neg.val = 1#u8 then Field51_as_Nat x_negated else Field51_as_Nat x := by
    unfold Field51_as_Nat
    split <;> rename_i h
    · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
      have := x1_post i hi; rw [if_pos h] at this
      exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
    · apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
      have := x1_post i hi; rw [if_neg h] at this
      exact congrArg (fun u => 2 ^ (51 * i) * u.val) this
  have hx1_select : x1.toField = if x_neg.val = 1#u8 then x_negated.toField else x.toField := by
    unfold FieldElement51.toField; rw [hx1_nat]; split <;> rfl
  have hx1_abs : x1.toField = math.abs_edwards x.toField := by
    rw [hx1_select, hx_negated_neg, math.abs_edwards, math.is_negative]
    by_cases hxn : x_neg.val = 1#u8
    · rw [if_pos hxn]
      have : (x.toField.val % 2 == 1) = true := by
        rw [beq_iff_eq]; unfold FieldElement51.toField; rw [ZMod.val_natCast]
        exact x_neg_post.mp hxn
      simp only [this, ↓reduceIte]
    · rw [if_neg hxn]
      have : (x.toField.val % 2 == 1) = false := by
        rw [Bool.eq_false_iff]; intro h; rw [beq_iff_eq] at h
        exact hxn (x_neg_post.mpr (by
          unfold FieldElement51.toField at h; rwa [ZMod.val_natCast] at h))
      simp only [this, Bool.false_eq_true, ↓reduceIte]
  have hI_sq_W : invsqrt.1.val = 1#u8 → invsqrt.2.toField ^ 2 * W = 1 := by
    intro h_ok1
    have h_nz : Field51_as_Nat v_u2_sqr % p ≠ 0 := by
      intro h_zero; exact absurd h_ok1 (by rw [(invsqrt_case1 h_zero).1]; decide)
    have h_ex : ∃ z : Nat, (z ^ 2 * (Field51_as_Nat v_u2_sqr % p)) % p = 1 := by
      by_contra h_nex; exact absurd h_ok1 (by rw [(invsqrt_case3 ⟨h_nz, h_nex⟩).1]; decide)
    have h_sq := (invsqrt_case2 ⟨h_nz, h_ex⟩).2
    rw [← h_v_u2_sqr_field]; unfold FieldElement51.toField
    have h := lift_mod_eq ((Field51_as_Nat invsqrt.2 % p) ^ 2 * (Field51_as_Nat v_u2_sqr % p)) 1
      (by rw [show (1 : Nat) % p = 1 from by decide]; exact h_sq)
    push_cast at h; simp only [ZMod.natCast_mod] at h; exact h
  -- Simplified coordinate expressions
  have hDy_simp : Dy.toField = invsqrt.2.toField ^ 2 * u2.toField * v.toField := by
    rw [hDy_field, hDx_v, hDx]; ring
  have hy_simp : y.toField = u1.toField * (invsqrt.2.toField ^ 2 * u2.toField * v.toField) := by
    rw [hy_field, hDy_simp]
  have hx_simp : x.toField = 2 * s.toField * invsqrt.2.toField * u2.toField := by
    rw [hx_field, hs_plus_s, hDx]; ring
  have h_valid_point
      (hI : invsqrt.2.toField ^ 2 * (v.toField * u2.toField ^ 2) = 1) :
      edwards.EdwardsPoint.IsValid { X := x1, Y := y, Z := one, T := t } := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- X_bounds
      change ∀ i < 5, x1[i]!.val < 2 ^ 53
      intro i hi; rw [x1_post i hi]; split
      · have := x_negated_post2 i hi; omega
      · have := x_post2 i hi; omega
    · -- Y_bounds
      change ∀ i < 5, y[i]!.val < 2 ^ 53
      intro i hi; have := y_post2 i hi; omega
    · -- Z_bounds
      change ∀ i < 5, one[i]!.val < 2 ^ 53
      intro i hi; have := one_post2 i hi; omega
    · -- T_bounds
      change ∀ i < 5, t[i]!.val < 2 ^ 53
      intro i hi; have := t_post2 i hi; omega
    · -- Z_ne_zero
      change one.toField ≠ 0
      rw [hONE]; exact one_ne_zero
    · -- T_relation
      change x1.toField * y.toField = t.toField * one.toField
      rw [ht_field, hONE, mul_one]
    · -- on_curve
      dsimp only
      simp only [hONE, one_pow, mul_one]
      have h_x1_sq : x1.toField ^ 2 = x.toField ^ 2 := by
        rw [hx1_abs]; exact abs_edwards_sq x.toField
      rw [h_x1_sq, hx_simp, hy_simp]
      exact on_curve_from_decompression Ed25519.a Ed25519.d s.toField
        invsqrt.2.toField u1.toField u2.toField v.toField
        (by simp only [Ed25519]) hu1_val hu2_val hv_val hI
  have h_step2_success_of_decompress (P : Point Ed25519)
      (h_decomp : ristretto.decompress_step2 s.toField = some P) :
      invsqrt.1.val = 1#u8 ∧ c.val = 0#u8 ∧ c1.val = 0#u8 ∧
        RistrettoPoint.toPoint { X := x1, Y := y, Z := one, T := t } = P := by
    have h_fwd := decompress_step2_forward s.toField P h_decomp
      u1.toField u2.toField v.toField W hu1_val hu2_val hv_val hW_eq
    obtain ⟨h_sq, h_W_ne, h_neg_fwd, h_y_ne_fwd, h_coords⟩ := h_fwd
    have h_ok1 : invsqrt.1.val = 1#u8 := by
      have h_nz := h_ne_bridge.mpr h_W_ne
      have h_ex := h_sq_bridge.mpr ⟨h_nz, h_sq⟩
      exact (invsqrt_case2 ⟨h_nz, h_ex⟩).1
    have hI := hI_sq_W h_ok1
    have ⟨h_Px, h_Py⟩ := h_coords invsqrt.2.toField hI
    have hx1_eq_Px : x1.toField = P.x := by rw [hx1_abs, hx_simp]; exact h_Px.symm
    have hy_eq_Py : y.toField = P.y := by rw [hy_simp]; exact h_Py.symm
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
    have h_valid := h_valid_point (by rw [← hW_eq]; exact hI)
    have hPt := edwards.EdwardsPoint.toPoint_of_isValid h_valid
    refine ⟨h_ok1, h_c, h_c1, ?_⟩
    ext
    · simp only [RistrettoPoint.toPoint, hPt.1, hONE, div_one, hx1_eq_Px]
    · simp only [RistrettoPoint.toPoint, hPt.2, hONE, div_one, hy_eq_Py]
  have h_decompress_of_step2_success (P : Point Ed25519)
      (h_success : invsqrt.1.val = 1#u8 ∧ c.val = 0#u8 ∧ c1.val = 0#u8 ∧
        RistrettoPoint.toPoint { X := x1, Y := y, Z := one, T := t } = P) :
      ristretto.decompress_step2 s.toField = some P := by
    rcases h_success with ⟨h_ok1, h_c, h_c1, h_pt⟩
    have hI_sq := hI_sq_W h_ok1
    have h_valid := h_valid_point (by rw [← hW_eq]; exact hI_sq)
    have ⟨hPx, hPy⟩ := toPoint_coords h_valid hONE h_pt
    have h_neg := is_negative_Pxy_false hPx hPy ht_field h_c c_post
    have h_y_ne := Py_ne_zero hPy h_c1 c1_post
    have hIW : invsqrt.2.toField ^ 2 * (v.toField * u2.toField ^ 2) = 1 := by
      rw [← hW_eq]; exact hI_sq
    exact decompress_step2_backward s.toField invsqrt.2.toField
      u1.toField u2.toField v.toField hu1_val hu2_val hv_val hIW P
      h_neg h_y_ne
      (by rw [hPx, hx1_abs, hx_simp])
      (by rw [hPy, hy_simp])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Goal 1: ok1 ↔ (v * u2² ≠ 0 ∧ IsSquare(v * u2²))
    constructor
    · intro h_ok
      have h_nz : Field51_as_Nat v_u2_sqr % p ≠ 0 := by
        intro h_zero; exact absurd h_ok (by rw [(invsqrt_case1 h_zero).1]; decide)
      have h_ex : ∃ x : Nat, (x ^ 2 * (Field51_as_Nat v_u2_sqr % p)) % p = 1 := by
        by_contra h_nex
        exact absurd h_ok (by rw [(invsqrt_case3 ⟨h_nz, h_nex⟩).1]; decide)
      exact ⟨h_ne_bridge.mp h_nz, (h_sq_bridge.mp h_ex).2⟩
    · -- ← direction
      intro ⟨h_ne, h_sq⟩
      have h_nz : Field51_as_Nat v_u2_sqr % p ≠ 0 := h_ne_bridge.mpr h_ne
      exact (invsqrt_case2 ⟨h_nz, h_sq_bridge.mpr ⟨h_nz, h_sq⟩⟩).1
  · -- Goal 2: c ↔ math.is_negative t.toField
    simp only [c_post, math.is_negative, FieldElement51.toField, ZMod.val_natCast, beq_iff_eq]
  · -- Goal 3: c1 ↔ y.toField = 0
    simp only [c1_post, FieldElement51.toField, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  · -- Goal 4: ∀ P, decompress_step2 ... ↔ ...
    intro P
    constructor
    · intro h_decomp
      exact h_step2_success_of_decompress P h_decomp
    · intro h_success
      exact h_decompress_of_step2_success P h_success
  · -- Goal 5: ok1=1 ∧ c=0 ∧ c1=0 → RistrettoPoint.IsValid pt
    intro ⟨h_ok1, _, _⟩
    have hI := hI_sq_W h_ok1
    unfold RistrettoPoint.IsValid
    refine ⟨?_, ?_⟩
    · -- Part 1: EdwardsPoint.IsValid { X := x1, Y := y, Z := one, T := t }
      exact h_valid_point (by rw [← hW_eq]; exact hI)
    · -- Part 2: IsSquare (Z² - Y²), i.e., IsSquare (1 - y²)
      dsimp only
      simp only [hONE, one_pow]
      have hIW : invsqrt.2.toField ^ 2 * (v.toField * u2.toField ^ 2) = 1 := by
        rw [← hW_eq]; exact hI
      have hW_ne : W ≠ 0 := by
        intro h; rw [h, mul_zero] at hI; exact one_ne_zero hI.symm
      have hu2_ne : u2.toField ≠ 0 := by
        intro h; exact hW_ne (by rw [hW_eq, h]; ring)
      -- Key identity: y · u2 = u1 (from I² · (v · u2²) = 1)
      have hyu2 : y.toField * u2.toField = u1.toField := by
        rw [hy_simp]; linear_combination u1.toField * hIW
      -- Witness: 1 - y² = (2s/u2)²
      refine ⟨2 * s.toField / u2.toField, ?_⟩
      have hu2_sq_ne : u2.toField ^ 2 ≠ 0 := pow_ne_zero 2 hu2_ne
      suffices h : (1 - y.toField ^ 2) * u2.toField ^ 2 = (2 * s.toField) ^ 2 by
        rw [show (2 * s.toField / u2.toField) * (2 * s.toField / u2.toField) =
          (2 * s.toField) ^ 2 / u2.toField ^ 2 from by ring]
        rw [eq_div_iff hu2_sq_ne]
        exact h
      -- Expand: (1 - y²) · u2² = u2² - (y · u2)² = u2² - u1²
      have : (1 - y.toField ^ 2) * u2.toField ^ 2 =
        u2.toField ^ 2 - (y.toField * u2.toField) ^ 2 := by ring
      rw [this, hyu2, hu1_val, hu2_val]
      -- (1+s²)² - (1-s²)² = 4s²
      ring

end curve25519_dalek.ristretto.decompress
