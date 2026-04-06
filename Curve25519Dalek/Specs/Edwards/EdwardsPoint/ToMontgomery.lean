/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Math.Montgomery.Representation
/-! # Spec Theorem for `EdwardsPoint::to_montgomery`

Specification and proof for `EdwardsPoint::to_montgomery`.

This function converts an EdwardsPoint from the twisted Edwards curve to the
corresponding MontgomeryPoint (only the u-coordinate) on the Montgomery curve,
using the birational map
u = (1+y)/(1-y) = (Z+Y)/(Z-Y).

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to a MontgomeryPoint (u-coordinate only), using the birational map:
  - u ≡ (1+y)/(1-y) ≡ (Z+Y)/(Z-Y) (mod p)

• Special case: when Y = Z (affine y = 1, the identity point on Edwards curve),
  the denominator is zero. Since 0.invert() = 0 in this implementation,
  this yields u = 0.

• The output u is represented as an U8x32 array (a type alias for MontgomeryPoint)

natural language specs:

• The function always succeeds (no panic)
• For the input Edwards point (X, Y, Z, T), the resulting MontgomeryPoint has u-coordinate:
  - If Z ≢ Y (mod p): u ≡ (Z+Y) * (Z-Y)^(-1) (mod p)
  - If Z ≡ Y (mod p): u ≡ 0 (mod p)
where p = 2^255 - 19
-/

/-!
## Key proof steps for `to_montgomery_birational_eq`

The proof establishes `fromEdwards e.toPoint = MontgomeryPoint.mkPoint a` given:
1. Bounds on the Edwards point limbs (h_Y_bounds, h_Z_bounds)
2. An arithmetic relationship (h_arith) between the Field51 limb representations of
   Y, Z and the byte representation of a.

The proof proceeds by:


**Step 2 – Identify u-coordinates.**
Show that the u-coordinate stored in `MontgomeryPoint.mkPoint a` (namely
`(U8x32_as_Field a)`) equals
`(1 + e.toPoint.y) / (1 - e.toPoint.y)`, the x-coordinate produced by `fromEdwards`.

**Step 3 – Identify v-coordinates.**
Both definitions choose a v satisfying `v^2 = u^3 + A*u^2 + u`:
- `fromEdwards` uses `v_ed = roots_B * (1 + y) / ((1 - y) * x)`.
- `u_affine_toPoint` uses `v_mont = (sqrt_checked (v_squared u)).1 = abs_edwards r`
  where `r^2 = v_squared u`.
Since `v_ed` is itself a square root of `v_squared u` (proved by `on_MontgomeryCurves`),
and `abs_edwards` picks the canonical (even-parity) square root, one shows
`v_ed = ±v_mont`. Equality (rather than negation) requires a parity argument
relating `roots_B` to the canonical root choice.

**Step 4 – Handle degenerate cases.**
- If `e.IsValid` is false, `e.toPoint = 0` and `fromEdwards 0 = 0`.
  The h_arith "if" branch then forces u ≡ 0, so `mkPoint a = T_point`.
  (Note: `0 ≠ T_point` as Weierstrass affine points; the identity case requires
  the additional hypothesis that the Edwards point is not the group identity,
  which is guaranteed by the valid-point invariant in practice.)
- If `e.toPoint.x = 0` (2-torsion), `fromEdwards` returns `T_point` and
  `mkPoint a` also returns `T_point` (since u = 0 there).

The full proof requires several supporting lemmas about `sqrt_checked`, `abs_edwards`,
`roots_B`, and the interaction of `% 2^255` with the field embedding.
-/

lemma mkPoint_u_zero (a : montgomery.MontgomeryPoint)
    (h : (U8x32_as_Field a) = 0) :
    MontgomeryPoint.mkPoint a = T_point := by
  unfold MontgomeryPoint.mkPoint MontgomeryPoint.u_affine_toPoint
  simp only [h, beq_self_eq_true]
  simp

private lemma v_coord_birational_match
    (e : Edwards.Point Edwards.Ed25519)
    (hy_ne_1 : e.y ≠ 1) (hx_ne_0 : e.x ≠ 0)
    (h_sqrt_true :
      (curve25519_dalek.math.sqrt_checked
        (v_squared ((1 + e.y) / (1 - e.y)))).2 = true) :
    (curve25519_dalek.math.sqrt_checked
      (v_squared ((1 + e.y) / (1 - e.y)))).1 =
    math.abs_edwards (Curve25519.roots_B * (1 + e.y) / ((1 - e.y) * e.x)) := by
  set u := (1 + e.y) / (1 - e.y) with hu_def
  set v_E := Curve25519.roots_B * (1 + e.y) / ((1 - e.y) * e.x) with hv_E_def
  have h_v_sq : v_E ^ 2 = v_squared u := by
    have h := on_MontgomeryCurves e hy_ne_1 hx_ne_0
    simp only at h
    simp only [v_squared]
    exact h
  have h_r_sq : (curve25519_dalek.math.sqrt_checked (v_squared u)).1 ^ 2 = v_squared u :=
    curve25519_dalek.math.sqrt_checked_spec (v_squared u)
      (Prod.mk.eta (p := curve25519_dalek.math.sqrt_checked (v_squared u))).symm h_sqrt_true
  have h_abs_eq : curve25519_dalek.math.abs_edwards
        (curve25519_dalek.math.sqrt_checked (v_squared u)).1 =
      curve25519_dalek.math.abs_edwards v_E :=
    curve25519_dalek.math.abs_edwards_eq_of_sq_eq (by rw [h_r_sq, h_v_sq])
  have h_is_sq : IsSquare (v_squared u) :=
    (curve25519_dalek.math.sqrt_checked_iff_isSquare (v_squared u)
      (Prod.mk.eta (p := curve25519_dalek.math.sqrt_checked (v_squared u))).symm).mp h_sqrt_true
  have h_r_unfold : (curve25519_dalek.math.sqrt_checked (v_squared u)).1 =
      curve25519_dalek.math.abs_edwards (Classical.choose h_is_sq) := by
    unfold curve25519_dalek.math.sqrt_checked
    rw [dif_pos h_is_sq]
  have h_r_not_neg : curve25519_dalek.math.is_negative
      (curve25519_dalek.math.sqrt_checked (v_squared u)).1 = false := by
    rw [h_r_unfold]
    exact curve25519_dalek.math.is_negative_abs_edwards _
  have h_r_canon : curve25519_dalek.math.abs_edwards
        (curve25519_dalek.math.sqrt_checked (v_squared u)).1 =
      (curve25519_dalek.math.sqrt_checked (v_squared u)).1 := by
    unfold curve25519_dalek.math.abs_edwards
    rw [h_r_not_neg]
    simp
  simp_all

private lemma y_eq_neg_one_of_x_eq_zero
    (e : Edwards.Point Edwards.Ed25519)
    (hx : e.x = 0) (hy_ne_1 : e.y ≠ 1) :
    e.y = -1 := by
  have hcurve := e.on_curve
  have : Edwards.Ed25519.a = -1 := rfl
  simp [hx, mul_zero, zero_mul, zero_add] at hcurve
  grind

private lemma x_eq_zero_of_y_eq_neg_one
    (e : Edwards.Point Edwards.Ed25519)
    (hy : e.y = -1) :
    e.x = 0 := by
  have hcurve := e.on_curve
  have ha1 : Edwards.Ed25519.a = -1 := rfl
  rw [hy, ha1, mul_comm] at hcurve
  simp only [neg_sq, one_pow] at hcurve
  have hxsq : e.x ^ 2 * (-1 - Edwards.Ed25519.d) = 0 := by linear_combination hcurve
  rcases mul_eq_zero.mp hxsq with h | h
  · exact pow_eq_zero_iff (by norm_num) |>.mp h
  · exfalso
    have : (-1 : CurveField) - Edwards.Ed25519.d ≠ 0 := by decide
    exact this h

private lemma birational_u_ne_zero_of_x_ne_zero
    (e : Edwards.Point Edwards.Ed25519)
    (hy_ne_1 : e.y ≠ 1) (hx : e.x ≠ 0) :
    (1 + e.y) / (1 - e.y) ≠ 0 := by
  intro h_zero
  have h1m : (1 : CurveField) - e.y ≠ 0 := sub_ne_zero.mpr (fun hc => hy_ne_1 (by grind))
  rw [div_eq_zero_iff] at h_zero
  have h1p : (1 : CurveField) + e.y = 0 := h_zero.resolve_right h1m
  have hy_m1 : e.y = -1 := by grind
  exact hx (x_eq_zero_of_y_eq_neg_one e hy_m1)

private lemma v_squared_isSquare_of_nonsingular
    (e : Edwards.Point Edwards.Ed25519)
    (a : montgomery.MontgomeryPoint)
    (hy_ne_1 : e.y ≠ 1) (hx : e.x ≠ 0)
    (hu_bira : (1 + e.y) / (1 - e.y) = (U8x32_as_Field a)) :
    IsSquare (v_squared (U8x32_as_Field a)) :=
  ⟨Curve25519.roots_B * (1 + e.y) / ((1 - e.y) * e.x), by
    have h_ns := nonsingular_on_curves_M e hy_ne_1 hx
    rw [WeierstrassCurve.Affine.nonsingular_iff] at h_ns
    have h_eq := h_ns.1
    rw [WeierstrassCurve.Affine.equation_iff] at h_eq
    simp only [MontgomeryCurveCurve25519] at h_eq
    rw [← hu_bira]
    unfold v_squared
    rw [← sq]
    grind⟩

theorem modEq_zero_iff (a n : ℕ) : a ≡ 0 [MOD n] ↔  a % n = 0 := by simp [Nat.ModEq]

lemma abs_T_point : abs_montgomery T_point = T_point:= by
  unfold T_point abs_montgomery
  simp

theorem to_montgomery_birational_zero
    (e : EdwardsPoint)
    (hvalid : e.IsValid)
    (n : ℕ)
    (hzy : Field51_as_Nat e.Z % p = Field51_as_Nat e.Y % p) :
    fromEdwards (n • e.toPoint) = 0 := by
  have hZY_eq : (Field51_as_Nat e.Z : CurveField) = Field51_as_Nat e.Y :=
      (Montgomery.lift_mod_eq_iff (Field51_as_Nat e.Z) (Field51_as_Nat e.Y)).mp hzy
  have he_zero : e.toPoint = 0 := by
    unfold EdwardsPoint.toPoint
    simp only [hvalid, ↓reduceDIte]
    apply zeroY
    have hy_val := (EdwardsPoint.toPoint_of_isValid hvalid).2
    simp only [toPoint, hvalid, ↓reduceDIte] at hy_val
    unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField at hy_val
    have:= hvalid.Z_ne_zero
    unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField at this
    rw [hy_val, ← hZY_eq, div_self this ]
  rw [he_zero, smul_zero, map_zero]

theorem to_montgomery_birational_eq
    (e : EdwardsPoint)
    (a : montgomery.MontgomeryPoint)
    (hvalid : e.IsValid)
    (h_arith :
      let Y := Field51_as_Nat e.Y
      let Z := Field51_as_Nat e.Z
      let u := U8x32_as_Nat a
      if Z % p = Y % p then
        u % p = 0
      else
        (u * Z) % p = (u * Y + (Z + Y)) % p)
      (hzy : Field51_as_Nat e.Z % p ≠ Field51_as_Nat e.Y % p) :
    abs_montgomery (fromEdwards e.toPoint) = MontgomeryPoint.mkPoint a := by
  simp only at h_arith
  simp only [hzy, ↓reduceIte] at h_arith
  have hne : (Field51_as_Nat e.Z : CurveField) ≠ Field51_as_Nat e.Y := by
    intro h
    exact hzy ((Montgomery.lift_mod_eq_iff _ _).mpr h)
  have h_field : (U8x32_as_Nat a : CurveField) * Field51_as_Nat e.Z =
        (U8x32_as_Nat a : CurveField) * Field51_as_Nat e.Y +
        ((Field51_as_Nat e.Z : CurveField) + Field51_as_Nat e.Y) := by
    have hme := (Montgomery.lift_mod_eq_iff
        (U8x32_as_Nat a * Field51_as_Nat e.Z)
        (U8x32_as_Nat a * Field51_as_Nat e.Y +
          (Field51_as_Nat e.Z + Field51_as_Nat e.Y))).mp h_arith
    push_cast [Nat.cast_mul, Nat.cast_add] at hme
    grind
  have hZmY_ne : (Field51_as_Nat e.Z : CurveField) - Field51_as_Nat e.Y ≠ 0 :=
      sub_ne_zero.mpr hne
  have h_u_eq : (U8x32_as_Nat a : CurveField) = (Field51_as_Nat e.Z + Field51_as_Nat e.Y) /
        (Field51_as_Nat e.Z - Field51_as_Nat e.Y) := by
      rw [eq_div_iff hZmY_ne]
      linear_combination h_field
  have h_u_0_eq : (U8x32_as_Field a) =
        (((Field51_as_Nat e.Z):CurveField) + Field51_as_Nat e.Y) /
        (((Field51_as_Nat e.Z):CurveField) - Field51_as_Nat e.Y) := by
      rw [U8x32_as_Field_eq_cast a, h_u_eq]
  have he_y := (EdwardsPoint.toPoint_of_isValid hvalid).2
  have hZ_ne : (Field51_as_Nat e.Z : CurveField) ≠ 0 := hvalid.Z_ne_zero
  have hy_ne_1 : e.toPoint.y ≠ 1 := by
    rw [he_y]
    intro h_eq
    apply hne
    unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField at h_eq
    field_simp at h_eq
    exact h_eq.symm
  have hu_bira : (1 + e.toPoint.y) / (1 - e.toPoint.y) = (U8x32_as_Field a) := by
    rw [h_u_0_eq, he_y]
    unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
    field_simp [hZ_ne]
  by_cases hx : e.toPoint.x = 0
  · unfold fromEdwards
    simp only [hy_ne_1]
    have hy_neg1 : e.toPoint.y = -1 := y_eq_neg_one_of_x_eq_zero e.toPoint hx hy_ne_1
    have h_u_0_zero : (U8x32_as_Field a) = 0 := by
      rw [← hu_bira, hy_neg1]; ring_nf
    have := mkPoint_u_zero a h_u_0_zero
    simp [this, hx, abs_T_point]
  · unfold fromEdwards
    simp only [hy_ne_1]
    simp only [↓reduceDIte, hx]
    have hu_0_ne : (U8x32_as_Field a) ≠ 0 := by
      rw [← hu_bira]
      exact birational_u_ne_zero_of_x_ne_zero e.toPoint hy_ne_1 hx
    have h_is_sq : IsSquare (v_squared (U8x32_as_Field a)) :=
          v_squared_isSquare_of_nonsingular e.toPoint a hy_ne_1 hx hu_bira
    have h_sqrt_true : (curve25519_dalek.math.sqrt_checked
              (v_squared (U8x32_as_Field a))).2 = true :=
          (curve25519_dalek.math.sqrt_checked_iff_isSquare
            (v_squared (U8x32_as_Field a))
            (Prod.mk.eta (p := curve25519_dalek.math.sqrt_checked
              (v_squared (U8x32_as_Field a)))).symm).mpr h_is_sq
    simp only [MontgomeryPoint.mkPoint, MontgomeryPoint.u_affine_toPoint, h_sqrt_true,
      Bool.not_true, hu_0_ne, beq_iff_eq]
    conv_rhs => simp only [↓reduceDIte]
    simp only [Bool.false_eq_true, ↓reduceDIte]
    apply abs_eq_some
    · exact hu_bira
    · have :=v_coord_birational_match e.toPoint hy_ne_1 hx
            (by rw [hu_bira]; exact h_sqrt_true)
      rw[hu_bira]  at this
      rw[this]

@[step]
theorem to_montgomery_spec (e : EdwardsPoint)
    (hvalid : e.IsValid)
    (h_Y_bounds : ∀ i < 5, e.Y[i]!.val < 2 ^ 53) (h_Z_bounds : ∀ i < 5, e.Z[i]!.val < 2 ^ 53) :
    to_montgomery e ⦃ mp =>
      let Y := Field51_as_Nat e.Y
      let Z := Field51_as_Nat e.Z
      let u := U8x32_as_Nat mp
      if Z % p = Y % p then
        u % p = 0 ∧ (∀ n : ℕ, fromEdwards (n • e.toPoint) = 0)
      else
      ((u * Z) % p = (u * Y + (Z + Y)) % p) ∧
      ( abs_montgomery (fromEdwards (e.toPoint)) = (MontgomeryPoint.mkPoint mp)) ⦄ := by
  unfold to_montgomery
  (step*; try grind)
  · have h_arith : (let Y := Field51_as_Nat e.Y; let Z := Field51_as_Nat e.Z;
        let u := U8x32_as_Nat a;
        if Z % p = Y % p then u % p = 0
        else  (u * Z) % p = (u * Y + (Z + Y)) % p) := by
      simp only
      split_ifs
      · rename_i h_zy
        have h_W_zero : Field51_as_Nat W % p = 0 := by
          rw [h_zy, ← Nat.ModEq] at W_post2
          conv_rhs at W_post2 => rw [← Nat.zero_add (Field51_as_Nat e.Y)]
          exact Nat.ModEq.add_right_cancel' (Field51_as_Nat e.Y) W_post2
        rw [a_post1, u_post1, Nat.mul_mod, fe_post2 h_W_zero, mul_zero, Nat.zero_mod]
      · rename_i h_zy
        have h_W_neq_zero : Field51_as_Nat W % p ≠ 0 := by
          intro h_contra
          rw [Nat.add_mod, h_contra, Nat.zero_add, Nat.mod_mod] at W_post2
          exact h_zy W_post2.symm
        have h_W_inv := fe_post1 h_W_neq_zero
        simp at h_W_inv
        ring_nf at h_W_inv
        have h_U_eq : Field51_as_Nat U = Field51_as_Nat e.Y + Field51_as_Nat e.Z := by
          unfold Field51_as_Nat
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [U_post1 i (Finset.mem_range.mp hi)]
          ring
        have h_elim : U8x32_as_Nat a * Field51_as_Nat W ≡
          Field51_as_Nat e.Y + Field51_as_Nat e.Z [MOD p] := by
          calc
            U8x32_as_Nat a * Field51_as_Nat W ≡
                Field51_as_Nat u * Field51_as_Nat W [MOD p] := by
                  simpa using a_post1.mul_right (Field51_as_Nat W)
            _ ≡ (Field51_as_Nat U * Field51_as_Nat fe) * Field51_as_Nat W [MOD p] := by
                  simpa using u_post1.mul_right (Field51_as_Nat W)
            _ ≡ Field51_as_Nat U [MOD p] := by
              rw [Nat.mul_assoc]
              simpa using @Nat.ModEq.mul_left p (Field51_as_Nat fe *
              Field51_as_Nat W) 1 (Field51_as_Nat U) h_W_inv
            _ ≡ Field51_as_Nat e.Y + Field51_as_Nat e.Z [MOD p] := by
                  unfold Nat.ModEq; simp only [h_U_eq]
        rw [Nat.mul_mod, ← W_post2, Nat.add_mod, ← Nat.mul_mod, Nat.mul_add, ← Nat.ModEq]
        ring_nf
        have h_sum : U8x32_as_Nat a * (Field51_as_Nat W % p) +
            U8x32_as_Nat a * (Field51_as_Nat e.Y % p)
            ≡ U8x32_as_Nat a * Field51_as_Nat W + U8x32_as_Nat a * Field51_as_Nat e.Y [MOD p] :=
            (Nat.ModEq.mul_left (U8x32_as_Nat a) (Nat.mod_modEq (Field51_as_Nat W) p)).add
            (Nat.ModEq.mul_left (U8x32_as_Nat a) (Nat.mod_modEq (Field51_as_Nat e.Y) p))
        refine h_sum.trans ?_
        rw [Nat.add_comm]
        have h_full := Nat.ModEq.add_left (U8x32_as_Nat a * Field51_as_Nat e.Y) h_elim
        grind
    split_ifs
    · rename_i h1
      simp only [h1, ↓reduceIte] at h_arith
      constructor
      · exact h_arith
      · intro n
        apply to_montgomery_birational_zero
        all_goals simp_all
    · rename_i h1
      have h_arith1:= h_arith
      simp only [h1, ↓reduceIte] at h_arith
      constructor
      · exact h_arith
      · rw [ to_montgomery_birational_eq e a hvalid h_arith1 h1]

end curve25519_dalek.edwards.EdwardsPoint
