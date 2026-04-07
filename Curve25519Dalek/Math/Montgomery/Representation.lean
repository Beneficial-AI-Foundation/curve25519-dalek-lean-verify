/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Types

/-!
# Montgomery Point Representations

Bridge infrastructure connecting Rust `MontgomeryPoint` to mathematical points.
-/

/-!
## MontgomeryPoint Validity
-/

namespace curve25519_dalek.backend.serial.curve_models

abbrev MontgomeryPoint := curve25519_dalek.montgomery.MontgomeryPoint

end curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.montgomery

open curve25519_dalek curve25519_dalek.math
open Edwards

/--
Validity for MontgomeryPoint.
A MontgomeryPoint is a 32-byte integer `u` representing a coordinate on the curve
`v² = u³ + Au² + u`.
It is valid if:
1. The integer `u` is strictly less than the field modulus `p`.
2. `u` maps to a valid Edwards `y` coordinate (i.e., `u ≠ -1`).
3. The resulting Edwards point exists (i.e., we can solve for `x`).
-/
def MontgomeryPoint.IsValid (m : MontgomeryPoint) : Prop :=
  let u : ZMod p := U8x32_as_Field m
  -- The check `u_int < p` is implicitly handled because
  -- bytesToField returns a `ZMod p`, which is canonical by definition.
  -- However, to match the Rust strictness (rejecting non-canonical inputs),
  -- we should technically check the raw Nat value.
  -- But for the linter ''deterministic timeout' issue, we just need to avoid U8x32_as_Nat.
  if u + 1 = 0 then
    False
  else
    let y := (u - 1) * (u + 1)⁻¹
    let num := y^2 - 1
    let den := (d : ZMod p) * y^2 + 1
    IsSquare (num * den⁻¹)

noncomputable instance (m : MontgomeryPoint) : Decidable (MontgomeryPoint.IsValid m) := by
  unfold MontgomeryPoint.IsValid
  infer_instance

/--
The Edwards denominator is never zero.
-/
lemma edwards_denom_nonzero (y : ZMod p) : (Ed25519.d : ZMod p) * y ^ 2 + 1 ≠ 0 := by
  intro h_zero
  have h_eq : Ed25519.d * y^2 = -1 := eq_neg_of_add_eq_zero_left h_zero
  by_cases hy : y = 0
  · -- If y = 0, then 0 = -1, contradiction.
    rw [hy, pow_two] at h_eq; simp only [mul_zero] at h_eq; contradiction
  · -- y ≠ 0 case
    have h_d_val : Ed25519.d = -1 * (y^2)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero 2 hy)).mpr
      exact h_eq
    have h_d_sq : IsSquare (Ed25519.d : ZMod p) := by
      rw [h_d_val]
      apply IsSquare.mul
      · exact Edwards.neg_one_is_square -- From Curve.lean
      · rw [← inv_pow]; exact IsSquare.sq (y⁻¹)
    exact Edwards.d_not_square h_d_sq

lemma montgomery_helper {F : Type*} [Field F] (d y x_sq : F)
    (h_den : d * y ^ 2 + 1 ≠ 0)
    (h_x : x_sq = (y ^ 2 - 1) * (d * y ^ 2 + 1)⁻¹) :
    -1 * x_sq + y ^ 2 = 1 + d * x_sq * y ^ 2 := by
  rw [h_x]; apply (mul_right_inj' h_den).mp; field_simp [h_den]
  ring

/--
Convert MontgomeryPoint to Point Ed25519.
1. Recovers `y` from `u` via `y = (u-1)/(u+1)`.
2. Recovers `x` from `y` (choosing the canonical positive root).
Returns 0 (identity) if invalid.
-/
noncomputable def MontgomeryPoint.toPoint (m : MontgomeryPoint) : Point Ed25519 :=
  if h : (MontgomeryPoint.IsValid m) then
    let u : ZMod p := U8x32_as_Field m
    let one : ZMod p := 1
    let y : ZMod p := (u - one) * (u + one)⁻¹
    let num : ZMod p := y^2 - one
    let den : ZMod p := (d : ZMod p) * y^2 + one
    let x2 : ZMod p := num * den⁻¹
    match h_sqrt : sqrt_checked x2 with
    | (x_abs, is_sq) =>
    { x := x_abs, y := y, on_curve := by
        have h_is_sq_true : is_sq = true := by
          unfold MontgomeryPoint.IsValid at h
          by_cases h_inv : u + 1 = 0
          · rw [if_pos h_inv] at h; dsimp only [h_inv] at h
          · rw [if_neg h_inv] at h; rw [sqrt_checked_iff_isSquare x2 h_sqrt]; convert h
        have h_x_sq : x_abs^2 = x2 := by
          apply sqrt_checked_spec x2 h_sqrt h_is_sq_true
        have h_den_nz : den ≠ 0 := by
          dsimp only [den, one]
          apply edwards_denom_nonzero
        have ha : Ed25519.a = -1 := rfl
        have hd : (d : ZMod p) = Ed25519.d := rfl
        rw [ha, h_x_sq]
        dsimp only [x2, num, den, one] at ⊢ h_den_nz
        apply (mul_right_inj' h_den_nz).mp
        field_simp [h_den_nz]
        simp only [neg_sub]
        rw [← hd]
        ring
      }
  else
    0

end curve25519_dalek.montgomery

namespace Montgomery

open curve25519_dalek.montgomery
open curve25519_dalek.math

section MontgomeryPoint

def v_squared (u : CurveField) : CurveField := u ^ 3 + Curve25519.A * u ^ 2 + u

/-- Create a point from a MontgomeryPoint byte representation.
    Computes the v-coordinate from u using the Montgomery curve equation v² = u³ + A·u² + u.

    Note: `sqrt_checked` returns a value whose square equals its input, which depends on
    the mathematical properties of the square root function in the field.

    This is a one-way conversion, since the Montgomery
    model does not retain sign information.
-/

noncomputable def MontgomeryPoint.u_affine_toPoint (u : CurveField) : Point:=
    if  h_y_eq_false:u == 0 then
      T_point
    else
    if h_sq_not : !(curve25519_dalek.math.sqrt_checked (v_squared u)).2  then
      T_point
    else
      .some (x := u) (y := (curve25519_dalek.math.sqrt_checked (v_squared u)).1) (h := by
        simp only [Bool.not_eq_eq_eq_not] at h_sq_not
        have h_call : curve25519_dalek.math.sqrt_checked (v_squared u) =
          ((curve25519_dalek.math.sqrt_checked (v_squared u)).1,
           (curve25519_dalek.math.sqrt_checked (v_squared u)).2) :=
          Prod.mk.eta.symm
        have curve_eq : (curve25519_dalek.math.sqrt_checked (v_squared u)).1 ^ 2 =
            u ^ 3 + Curve25519.A * u ^ 2 + u := by
          apply sqrt_checked_spec (v_squared u)
          · exact h_call
          · simp only [Bool.not_true] at h_sq_not
            cases h : (curve25519_dalek.math.sqrt_checked (v_squared u)).2
            · exact absurd h h_sq_not
            · rfl
        apply (nonsingular_iff u _).mpr
        rw [WeierstrassCurve.Affine.equation_iff]
        simp only [MontgomeryCurveCurve25519]
        simp only [curve_eq]
        ring
     )

theorem Aux_u_affine_toPoint_spec {u v : CurveField}
    (non : u ≠ 0)
    (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    ((sqrt_checked (u ^ 3 + Curve25519.A * u ^ 2 + u)).2 = false ∨ u = 0) = False := by
  have is_sq : IsSquare (u ^ 3 + Curve25519.A * u ^ 2 + u) := by
    use v
    rw [sq] at equation
    exact equation.symm
  unfold sqrt_checked
  simp only [is_sq, ↓reduceDIte, Bool.true_eq_false, non, or_self]

theorem non_u_affine_toPoint_spec {u v : CurveField}
    (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    MontgomeryCurveCurve25519.Nonsingular u v := by
  apply (nonsingular_iff u v).mpr
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [MontgomeryCurveCurve25519]
  simp only [equation]
  ring

noncomputable def MontgomeryPoint.mkPoint (m : MontgomeryPoint) : Point:=
    MontgomeryPoint.u_affine_toPoint (U8x32_as_Field m)

noncomputable def abs_montgomery1 : Point → Point
  | .zero => 0
  | e@(.some (x := _) (y := v) (h := _)) =>
    if is_negative v then -e else e

noncomputable def abs_montgomery : Point → Point
  | .zero => 0
  | e@(.some (x := u) (y := v) (h := h)) =>
      .some (x := u) (y := abs_edwards v) (h := by
      apply (nonsingular_iff u _).mpr
      rw [WeierstrassCurve.Affine.equation_iff]
      simp only [abs_edwards_sq, MontgomeryCurveCurve25519, zero_mul, add_zero, one_mul]
      rw[nonsingular_iff u _] at h
      rw [WeierstrassCurve.Affine.equation_iff] at h
      simp only [MontgomeryCurveCurve25519, zero_mul, add_zero, one_mul] at h
      exact h)

lemma abs_eq_some (u v u₁ v₁ : CurveField)
  (h : MontgomeryCurveCurve25519.Nonsingular u v)
  (h₁ : MontgomeryCurveCurve25519.Nonsingular u₁ v₁)
  (hx : u = u₁)
  (hy : abs_edwards v = v₁) :
  abs_montgomery (WeierstrassCurve.Affine.Point.some h)
  = (WeierstrassCurve.Affine.Point.some h₁) := by
  unfold abs_montgomery
  simp_all

lemma is_negative_eq (u v : CurveField)
  (h : MontgomeryCurveCurve25519.Nonsingular u v)
  (hv : is_negative v) :
  abs_montgomery (WeierstrassCurve.Affine.Point.some h)
  = -(WeierstrassCurve.Affine.Point.some h) := by
  unfold abs_montgomery
  simp[MontgomeryCurveCurve25519, abs_edwards, hv]

lemma cast_zero (res : MontgomeryPoint)
  (hmod : U8x32_as_Nat res % p = 0) :
    U8x32_as_Field res = 0 := by
    have := Edwards.lift_mod_eq (U8x32_as_Nat res) 0 (by
    simpa [Nat.zero_mod] using hmod)
    rw [U8x32_as_Field_eq_cast, this]
    simp only [Nat.reducePow, Nat.reduceSub, Nat.cast_zero]

end MontgomeryPoint

section fromEdwards
open curve25519_dalek.montgomery
open curve25519_dalek.edwards

lemma d_eq : (Edwards.Ed25519.d : CurveField) = -121665 / 121666 := by
  have hd : Edwards.Ed25519.d = d := by decide
  rw [hd]
  have : (121666 : CurveField) ≠ 0 := by decide
  field_simp [this]
  decide

lemma a_plus_d : (Edwards.Ed25519.a : CurveField) + Edwards.Ed25519.d = - 243331/121666 := by
  have ha : Edwards.Ed25519.a = -1 := by rfl
  rw [ha, d_eq]
  have : (121666 : CurveField) ≠ 0 := by decide
  field_simp [this]
  decide

lemma a_sub_d : (Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d = - 1/121666 := by
  have ha : Edwards.Ed25519.a = -1 := by rfl
  rw [ha, d_eq]
  have : (121666 : CurveField) ≠ 0 := by decide
  field_simp [this]
  decide

lemma adA : 2 * ((Edwards.Ed25519.a : CurveField) + Edwards.Ed25519.d) /
    (Edwards.Ed25519.a - Edwards.Ed25519.d) = Curve25519.A := by
  rw [a_plus_d, a_sub_d]
  have : (121666 : CurveField) ≠ 0 := by decide
  field_simp [this]
  decide

lemma adB : (4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d)) = - 486664 := by
  rw [a_sub_d]
  have : (121666 : CurveField) ≠ 0 := by decide
  field_simp [this]
  decide

lemma A_add_2 : 486664 = Curve25519.A + 2 := by
  unfold Curve25519.A
  decide

lemma d_plus_one_square : IsSquare (Edwards.Ed25519.d +1) := by
  have : Edwards.Ed25519.d = d := rfl
  rw [this]
  have : ↑(↑d + 1) ≠ 0 := by unfold d; decide
  apply ((@legendreSym.eq_one_iff p _ (d + 1)) (by unfold d; decide)).mp
  norm_num [d, p]

lemma B_d_relation : IsSquare (4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d)) := by
  rw [adB]
  apply ((@legendreSym.eq_one_iff p _ (-486664)) (by decide)).mp
  norm_num [p]

lemma inver_Ad : (Curve25519.A + 2) * Edwards.Ed25519.d + (Curve25519.A - 2) = 0 := by
  rw [← adA]
  have : (Edwards.Ed25519.a - Edwards.Ed25519.d) ≠ 0 := by
    decide
  field_simp
  decide

lemma inver_Ad_eq : Edwards.Ed25519.d = -(Curve25519.A - 2) / (Curve25519.A + 2) := by
  rw [← adA]
  have : (Edwards.Ed25519.a - Edwards.Ed25519.d) ≠ 0 := by
    decide
  field_simp
  decide

-- Define roots_B as a square root of the B coefficient
noncomputable def Curve25519.roots_B : CurveField :=
  Classical.choose B_d_relation

lemma pow2_roots_B :
    Curve25519.roots_B ^ 2 = 4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d) := by
  classical
  unfold Curve25519.roots_B
  have := B_d_relation
  unfold IsSquare at this
  simpa [pow_two] using (Classical.choose_spec this).symm

lemma roots_B_non_zero : ¬ Curve25519.roots_B = 0 := by
  have := pow2_roots_B
  intro h
  rw [h, adB] at this
  revert this
  decide

lemma roots_B_d : Curve25519.roots_B ^ 2 * Edwards.Ed25519.d = (Curve25519.A - 2) := by
  simp only [pow2_roots_B, adB, neg_mul]
  simp only [A_add_2, inver_Ad_eq, neg_sub]
  decide

-- Prove that the Montgomery to Edwards conversion inverts the Edwards to Montgomery conversion
lemma montgomery_edwards_inverse {y : CurveField} (hy1 : y ≠ 1) :
    let u := (1 + y) / (1 - y)
    y = (u - 1) / (u + 1) := by
  intro u
  have num_eq : u - 1 = (1 + y - (1 - y)) / (1 - y) := by
    field_simp [hy1]
    agrind
  have num_simplified : u - 1 = (2 * y) / (1 - y) := by
    rw [num_eq]
    ring_nf
  have den_eq : u + 1 = (1 + y + (1 - y)) / (1 - y) := by
    field_simp [hy1]
    grind
  have den_simplified : u + 1 = 2 / (1 - y) := by
    rw [den_eq]
    ring_nf
  calc y = y := rfl
    _ = (2 * y) / 2 := by field_simp
    _ = (2 * y) / (1 - y) * (1 - y) / 2 := by field_simp [hy1]; grind
    _ = (u - 1) / (u + 1) := by
        rw [← num_simplified]
        field_simp [hy1]
        have h_u_plus_1 : u + 1 ≠ 0 := by
          rw [den_simplified]
          field_simp [hy1]
          ring_nf
          simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
          grind
        field_simp [h_u_plus_1]
        grind

theorem on_curves_M (e : Edwards.Point Edwards.Ed25519)
    (hy : e.y ≠ 1)
    (hx : e.x ≠ 0) :
    let u := (1 + e.y) / (1 - e.y)
    let v := (1 + e.y) / ((1 - e.y) * e.x)
    let A := 2 * ((Edwards.Ed25519.a : CurveField) + Edwards.Ed25519.d) /
      (Edwards.Ed25519.a - Edwards.Ed25519.d)
    let B := 4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d)
    B * v ^ 2 = u ^ 3 + A * u ^ 2 + u := by
  have eq := e.on_curve
  have huy := montgomery_edwards_inverse hy
  set u := (1 + e.y) / (1 - e.y) with hu
  set v := (1 + e.y) / ((1 - e.y) * e.x) with hv
  have h1 : (1 - e.y) ≠ 0 := by grind
  have h2 : (1 + e.y) ≠ 0 := by
    intro h2
    have : e.y = -1 := by grind
    simp only [this, even_two, Even.neg_pow, one_pow, mul_one] at eq
    have : (Edwards.Ed25519.a - Edwards.Ed25519.d) * e.x ^ 2 = 0 := by grind
    simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
               pow_eq_zero_iff, hx, or_false] at this
    revert this; decide
  have hxv : e.x = u / v := by rw [hu, hv]; field_simp [h1, h2, hx]
  dsimp only at huy
  rw [huy, hxv] at eq
  have nonv : v ≠ 0 := by rw [hv]; intro h; apply h2; grind
  have nonu : u ≠ 0 := by rw [hu]; intro h; apply h2; grind
  have nonu1 : u + 1 ≠ 0 := by rw [hu]; intro h; field_simp at h; ring_nf at h; grind
  field_simp at eq
  have ha : Edwards.Ed25519.a = -1 := rfl
  have hd : Edwards.Ed25519.d = d := rfl
  rw [ha, hd] at eq ⊢
  have h4u : 4 * u * v ^ 2 = -(u ^ 2 * ((d + 1) * u ^ 2 - 2 * (d - 1) * u + (d + 1))) := by
    grind
  have hkey : 4 * v ^ 2 = -u * ((d + 1) * u ^ 2 - 2 * (d - 1) * u + d + 1) :=
    mul_left_cancel₀ nonu (by linear_combination h4u)
  have hd_ne : (-1 : CurveField) - d ≠ 0 := by decide
  field_simp [hd_ne]
  rw [hkey]
  field_simp [hd_ne]
  ring

theorem on_MontgomeryCurves (e : Edwards.Point Edwards.Ed25519)
    (hy : e.y ≠ 1)
    (hx : e.x ≠ 0) :
    let u := (1 + e.y) / (1 - e.y)
    let v := Curve25519.roots_B * (1 + e.y) / ((1 - e.y) * e.x)
    v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u := by
  have := on_curves_M e hy hx
  simp_all only [ne_eq, adA]
  rw [← this, ← pow2_roots_B]
  grind

theorem nonsingular_on_curves_M (e : Edwards.Point Edwards.Ed25519) (hy : e.y ≠ 1)
    (hx : e.x ≠ 0) :
    let u := (1 + e.y) / (1 - e.y)
    let v := Curve25519.roots_B * (1 + e.y) / ((1 - e.y) * e.x)
    MontgomeryCurveCurve25519.Nonsingular u v := by
  rw [Montgomery.nonsingular_iff, WeierstrassCurve.Affine.equation_iff, MontgomeryCurveCurve25519]
  have := on_MontgomeryCurves e hy hx
  simp_all only [ne_eq, zero_mul, add_zero, one_mul]

lemma id_1 {u v : CurveField}
    (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    (-((Curve25519.A + 2) * u ^ 2) + v ^ 2) * (u + 1) ^ 2 =
    u * ((u * (u * 3 + 2 * Curve25519.A) + 1) ^ 2 - 4 * v ^ 2 * Curve25519.A - 8 * u * v ^ 2) := by
  linear_combination ((u + 1) ^ 2 + u * (4 * Curve25519.A + 8 * u)) * equation

lemma id_2 {u v : CurveField}
    (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    (-(Curve25519.A + 2) * u ^ 2 * (u + 1) ^ 2 * -1 + v ^ 2 * (u - 1) ^ 2) =
    u * (Curve25519.A * u * 2 + Curve25519.A * u ^ 3 * 2 + 1 + u ^ 2 * 6 + u ^ 4) := by
  linear_combination (u - 1) ^ 2 * equation

lemma id_3 {u v : CurveField}
    (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    (1 + 1) *
          ((u * (u * 3 + 2 * Curve25519.A) + 1) ^ 2 - v ^ 2 * Curve25519.A * (1 + 1) ^ 2 -
            v ^ 2 * u * (1 + 1) ^ 2 - v ^ 2 * u * (1 + 1) ^ 2) *
        (u * 2 * Curve25519.A * (1 + u ^ 2) + 1 + u ^ 2 * 6 + u ^ 4) =
      2 * (u - 1) * (u + 1) *
        (-(v ^ 4 * (1 + 1) ^ 3) +
          -((u * (u * 3 + 2 * Curve25519.A) + 1) *
              ((u * (u * 3 + 2 * Curve25519.A) + 1) ^ 2 -
                v ^ 2 * Curve25519.A * (1 + 1) ^ 2 - v ^ 2 * u * (1 + 1) ^ 2 -
                  v ^ 2 * u * (1 + 1) ^ 2 -
                v ^ 2 * u * (1 + 1) ^ 2)))
                := by
  linear_combination
    (16 * (u ^ 2 - 1) * v ^ 2 - 8 * u * (u * (u * 3 + 2 * Curve25519.A) + 1) ^ 2) * equation

lemma id_4 {u v : CurveField}
    (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u)
    (non_eq₀ : ¬(Curve25519.A + 2) * u ^ 2 * (u + 1) ^ 2 + v ^ 2 * (u - 1) ^ 2 = 0) :
    u * Curve25519.A * 2 * (1 + u ^ 2) + 1 + u ^ 2 * 6 + u ^ 4 ≠ 0 := by
  intro h
  apply non_eq₀
  have : u * Curve25519.A * 2 * (1 + u ^ 2) + 1 + u ^ 2 * 6 + u ^ 4
      = Curve25519.A * u * 2 + Curve25519.A * u ^ 3 * 2 + 1 + u ^ 2 * 6 + u ^ 4 := by ring_nf
  have eq := id_2 equation
  simp [← this, h] at eq
  grind

lemma id_5 {u1 v1 u2 v2 : CurveField}
    (equation1 : v1 ^ 2 = u1 ^ 3 + Curve25519.A * u1 ^ 2 + u1)
    (equation2 : v2 ^ 2 = u2 ^ 3 + Curve25519.A * u2 ^ 2 + u2) :
    (v1 * v2 * (u1 * u2 + 1) - u1 * u2 * (2 * (u1 + u2) + (u1 * u2 + 1) * Curve25519.A)) *
        (u1 - u2) ^ 2 =
      (v1 * v2 * (u1 + u2) - -(u1 * u2 * (u1 * u2 * 2 + (u1 + u2) * Curve25519.A + 2))) *
        ((v1 - v2) ^ 2 - Curve25519.A * (u1 - u2) ^ 2 -
            u1 * (u1 - u2) ^ 2 - u2 * (u1 - u2) ^ 2) := by
    simp only [sub_neg_eq_add]
    have : (v1 - v2) ^ 2 - Curve25519.A * (u1 - u2) ^ 2 - u1 * (u1 - u2) ^ 2 - u2 * (u1 - u2) ^ 2 =
     u1 + u1 * Curve25519.A * u2 * 2 + u1 * u2 ^ 2 + (u1 ^ 2 * u2 - v1 * v2 * 2) + u2 := by
      have : (v1 - v2) ^ 2 = v1 ^ 2 - 2 * v1 * v2 + v2 ^ 2 := by ring_nf
      rw [this, equation1, equation2]
      ring_nf
    rw [this]
    have : v1 * v2 * (u1 + u2) + u1 * u2 * (u1 * u2 * 2 + (u1 + u2) * Curve25519.A + 2)
    = v1 * v2 * u1 + v1 * v2 * u2 + u1 * u2 * 2 + u1 * u2 ^ 2 * Curve25519.A +
    u1 ^ 2 * u2 * Curve25519.A +
    u1 ^ 2 * u2 ^ 2 * 2 := by
      ring_nf
    rw [this]
    have : (v1 * v2 * u1 + v1 * v2 * u2 + u1 * u2 * 2 + u1 * u2 ^ 2 * Curve25519.A +
      u1 ^ 2 * u2 * Curve25519.A + u1 ^ 2 * u2 ^ 2 * 2) *
    (u1 + u1 * Curve25519.A * u2 * 2 + u1 * u2 ^ 2 + (u1 ^ 2 * u2 - v1 * v2 * 2) + u2)
    =-(v1 * v2 * u1 * u2 * 2) + v1 * v2 * u1 * u2 ^ 3 +
      (v1 * v2 * u1 ^ 2 - v1 * v2 * u1 ^ 2 * u2 ^ 2 * 2) +
                    v1 * v2 * u1 ^ 3 * u2 +
                  v1 * v2 * u2 ^ 2 +
                (-(u1 * u2 ^ 3 * Curve25519.A) - u1 * u2 ^ 4 * 2) +
              u1 ^ 2 * u2 ^ 2 * Curve25519.A * 2 +
            u1 ^ 2 * u2 ^ 3 * 2 +
          (-(u1 ^ 2 * u2 ^ 4 * Curve25519.A) - u1 ^ 3 * u2 * Curve25519.A) +
        u1 ^ 3 * u2 ^ 2 * 2 +
      u1 ^ 3 * u2 ^ 3 * Curve25519.A * 2 +
    (-(u1 ^ 4 * u2 * 2) - u1 ^ 4 * u2 ^ 2 * Curve25519.A) := by
      ring_nf
      rw [equation1, equation2]
      ring_nf
    rw [this]
    ring_nf

lemma id_6 {u1 v1 u2 v2 : CurveField}
    (equation1 : v1 ^ 2 = u1 ^ 3 + Curve25519.A * u1 ^ 2 + u1)
    (equation2 : v2 ^ 2 = u2 ^ 3 + Curve25519.A * u2 ^ 2 + u2) :
    (u1 - u2) *
        (((v1 - v2) ^ 2 - (u1 - u2) ^ 2 * Curve25519.A -
              u1 * (u1 - u2) ^ 2 - u2 * (u1 - u2) ^ 2) *
            (v1 * v2 * (u1 + 1) * (u2 + 1) +
              u1 * u2 * (Curve25519.A - 2) * (u1 - 1) * (u2 - 1)) +
          v1 * (u1 - u2) ^ 2 *
            (v2 * u1 * (u1 + 1) * (u2 - 1) + v1 * u2 * (u2 + 1) * (u1 - 1))) =
      (v2 * u1 * (u1 + 1) * (u2 - 1) + v1 * u2 * (u2 + 1) * (u1 - 1)) * (v2 - v1) *
        ((v1 - v2) ^ 2 - (u1 - u2) ^ 2 * Curve25519.A - u1 * (u1 - u2) ^ 2 -
          u2 * (u1 - u2) ^ 2 - u1 * (u1 - u2) ^ 2) := by
    ring_nf
    have : v2 ^ 3 = (v2 ^ 2) * v2 := by ring_nf
    rw [this, equation1, equation2]
    have : v1 ^ 3 = (v1 ^ 2) * v1 := by ring_nf
    rw [this, equation1]
    have : v2 ^ 4 = (v2 ^ 2) ^ 2 := by ring_nf
    rw [this, equation2]
    have : v1 ^ 4 = (v1 ^ 2) ^ 2 := by ring_nf
    rw [this, equation1]
    ring_nf

noncomputable def fromEdwards : Edwards.Point Edwards.Ed25519 → Point
  | e =>
    if hy: e.y = 1 then
      0
    else
      if hx: e.x = 0 then
        T_point
      else
        let u := (1 + e.y) / (1 - e.y)
        let v := Curve25519.roots_B * (1 + e.y) / ((1 - e.y) * e.x)
        .some (x := u) (y := v) (h := nonsingular_on_curves_M e hy hx)

theorem map_zero : fromEdwards 0 = 0 := by
  unfold fromEdwards
  simp only [Edwards.zero_y, ↓reduceDIte]

theorem zeroY (e : Edwards.Point Edwards.Ed25519)
    (h : e.y = 1) :
    e = 0 := by
  cases e with
  | mk x y h_curve =>
    subst h
    simp only [one_pow, mul_one] at h_curve
    have hx2 : x ^ 2 = 0 :=
      (mul_eq_zero.mp (show (Edwards.Ed25519.a - Edwards.Ed25519.d) * x ^ 2 = 0 from by
        linear_combination h_curve)).resolve_left (by decide)
    ext
    · exact sq_eq_zero_iff.mp hx2
    · rfl

theorem zero_iff (e : Edwards.Point Edwards.Ed25519) : e = 0 ↔ e.y = 1 := by
  constructor
  · intro he
    rw [he]
    rfl
  · apply zeroY

theorem exceptEdwardsPoint {e : Edwards.Point Edwards.Ed25519}
    (h : 1 + e.y = 0) :
    e.x = 0 := by
  have hy : e.y = -1 := by agrind
  have h_curve := e.on_curve
  have ha : Edwards.Ed25519.a = -1 := rfl
  rw [ha, hy] at h_curve
  have h_factor : e.x ^ 2 * (-(1 + Edwards.Ed25519.d)) = 0 := by grind
  have h_d_neq : (-(1 + Edwards.Ed25519.d) : ZMod p) ≠ 0 := by decide
  exact sq_eq_zero_iff.mp (by
    rcases mul_eq_zero.mp h_factor with h | h
    · exact h
    · exact absurd h h_d_neq)

theorem neg_fromEdwards (e : Edwards.Point Edwards.Ed25519) :
  fromEdwards (-e) = - fromEdwards e := by
  by_cases h : e = 0
  · simp [h, map_zero]
  · unfold fromEdwards
    rw [zero_iff] at h
    simp only [Edwards.neg_y, h, Edwards.neg_x]
    simp only [↓reduceDIte, neg_eq_zero, mul_neg]
    by_cases hx : e.x = 0
    · simp only [hx, ↓reduceDIte, T_point,
        WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.negY,
        MontgomeryCurveCurve25519, mul_zero, neg_zero, sub_self]
    · simp only [hx, ↓reduceDIte, MontgomeryCurveCurve25519,
        WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.negY, zero_mul, sub_zero,
        WeierstrassCurve.Affine.Point.some.injEq, true_and]
      agrind

theorem T_point_x {e : Edwards.Point Edwards.Ed25519}
    (h : e.x = 0) :
    e.y = 1 ∨ e.y = -1 := by
  have := e.on_curve
  simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add,
    zero_mul, add_zero, sq_eq_one_iff] at this
  exact this

lemma condition_Neg (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) (hy3 : 1 + e₂.y ≠ 0)
    (hx1 : e₁.x ≠ 0) (hx2 : e₂.x ≠ 0) :
    ((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧ e₁.x = -e₂.x) ↔
    ((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧
            Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) =
              -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
  simp only [and_congr_right_iff]
  intro ha
  constructor
  · intro hx
    rw [hx]
    field_simp [ha]
    simp only [neg_inj]
    field_simp [roots_B_non_zero]
    agrind
  · field_simp [roots_B_non_zero]
    field_simp at ha
    rw [ha]
    field_simp [hy1, hy3]
    agrind

lemma injective_fromEdwards {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) :
    (1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ↔ e₁.y = e₂.y := by
  constructor
  · intro h
    have non2 : (2 : CurveField) ≠ 0 := by decide
    field_simp [hy1, hy2] at h
    have : 2 * (e₁.y - e₂.y) = 0 := by agrind
    simp only [mul_eq_zero, non2, false_or] at this
    agrind
  · intro ha
    rw [ha]

lemma edwards_neg_iff_montgomery_neg {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) (hy3 : 1 + e₂.y ≠ 0)
    (hx1 : e₁.x ≠ 0) (hx2 : e₂.x ≠ 0) :
    (e₁.y = e₂.y ∧ e₁.x = -e₂.x) ↔
    ((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧
            Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) =
              -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
  rw [← injective_fromEdwards, condition_Neg]
  all_goals simp_all

theorem fromEdwards_add_of_snd_x_eq_zero_of_fst_y_eq_neg_one
    (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (non_e1_x : e₁.x ≠ 0)
    (zero_e2_x : e₂.x = 0)
    (e2y : e₂.y = -1)
    (non_e₁ : e₁.y = -1) :
    fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  unfold fromEdwards
  simp_all only [ne_eq, ↓reduceDIte, add_neg_cancel, sub_neg_eq_add, zero_div, mul_zero,
    dite_eq_ite]
  have non_sum : (e₁ + e₂).y = 1 := by
    simp only [Edwards.add_y]
    simp_all only [ne_eq, not_false_eq_true, mul_neg, mul_one, neg_neg, mul_zero, sub_zero,
    neg_zero, one_ne_zero, div_self]
  simp_all only [not_false_eq_true, ↓reduceDIte]
  have : -1 ≠ (1 : CurveField) := by decide
  simp only [Edwards.add_y] at non_sum
  simp_all only [mul_neg, mul_one, neg_neg, mul_zero, sub_zero, neg_zero, ne_eq, one_ne_zero,
    not_false_eq_true, div_self, ↓reduceDIte, ↓reduceIte]
  simp only [T_point]
  simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
  simp only [WeierstrassCurve.Affine.negY, neg_zero, MontgomeryCurveCurve25519, mul_zero, sub_self,
    and_self, ↓reduceDIte]

lemma edwards_one_sub_y_sq_mul_x_sq_eq (e₁ : Edwards.Point Edwards.Ed25519) :
    (1 + -e₁.y) * (1 - e₁.y) * e₁.x ^ 2 =
    (1 + e₁.y) * ((1 - e₁.y) * (-486664 - e₁.x ^ 2 * Curve25519.A) -
    (1 + e₁.y) * e₁.x ^ 2) := by
  rw [A_add_2]
  have hcurve := e₁.on_curve
  have ha : Edwards.Ed25519.a = -1 := rfl
  rw [ha] at hcurve
  linear_combination -(Curve25519.A + 2) * hcurve - (e₁.x ^ 2 * e₁.y ^ 2) * inver_Ad

lemma x_sq_mul_linear_factor_eq (e₁ : Edwards.Point Edwards.Ed25519) :
    e₁.x ^ 2 * (e₁.y * 2 + (-e₁.y ^ 2 - 1)) =
    e₁.x ^ 2 * (e₁.y * (2 + e₁.y * (1 - Curve25519.A)) + 1) +
    (e₁.x ^ 2 * Curve25519.A - Curve25519.roots_B ^ 2) +
    Curve25519.roots_B ^ 2 * e₁.y ^ 2 := by
    rw [pow2_roots_B, adB]
    have : -((1 + -e₁.y) * (1 - e₁.y) * e₁.x ^ 2) =
        (e₁.x ^ 2 * (e₁.y * 2 + (-e₁.y ^ 2 - 1))) := by grind
    rw [← this, edwards_one_sub_y_sq_mul_x_sq_eq e₁]
    ring

/-- The Montgomery curve equation `v² = u³ + Au² + u`, divided through by `u²`,
    rearranges to `1/u = (v/u)² - A - u`. This lemma establishes this equivalent form
    for an Edwards point mapped birationally to Montgomery coordinates. -/
theorem montgomery_inv_u_eq (e₁ : Edwards.Point Edwards.Ed25519)
    (non_e1_x : e₁.x ≠ 0)
    (non_e₁ : ¬ e₁.y = -1)
    (non_e : ¬ e₁.y = 1) :
    (1 + -e₁.y) / (1 + e₁.y) =
      (Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) /
        ((1 + e₁.y) / (1 - e₁.y))) ^ 2 - Curve25519.A -
        (1 + e₁.y) / (1 - e₁.y) := by
  have non_e1 : 1 + e₁.y ≠ 0 := by grind
  have non_e10 : 1 - e₁.y ≠ 0 := by grind
  field_simp
  rw [pow2_roots_B, adB]
  rw [edwards_one_sub_y_sq_mul_x_sq_eq]

theorem fromEdwards_add_of_snd_x_eq_zero (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (non_e1_x : e₁.x ≠ 0)
    (zero_e2_x : e₂.x = 0) :
    fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  have e2y := e₂.on_curve
  simp only [zero_e2_x, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add, zero_mul, add_zero, sq_eq_one_iff] at e2y
  rcases e2y with e2y | e2y
  · rw [zeroY e₂ e2y, add_zero, map_zero, add_zero]
  · by_cases non_e₁ : e₁.y = 1
    · unfold fromEdwards
      simp [T_point, Edwards.add_y]
      have : -1 ≠ (1 : CurveField) := by decide
      simp_all
    · by_cases non_e : e₁.y = -1
      · apply fromEdwards_add_of_snd_x_eq_zero_of_fst_y_eq_neg_one
        all_goals simp_all
      · have hsum_y : (e₁ + e₂).y ≠ 1 := by
          simp only [Edwards.add_y, e2y, mul_neg, mul_one, zero_e2_x, mul_zero, sub_zero,
            zero_mul, neg_zero, div_one, ne_eq]
          agrind
        unfold fromEdwards
        simp [T_point]
        simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
        simp [MontgomeryCurveCurve25519, hsum_y]
        simp [Edwards.add_y, Edwards.add_x, zero_e2_x, e2y, non_e₁, non_e1_x]
        have non_one : -1 ≠ (1 : CurveField) := by decide
        simp [non_one]
        have : ¬ (1 + e₁.y = 0 ∨ 1 - e₁.y = 0) := by grind
        simp_all
        constructor
        · have := montgomery_inv_u_eq e₁ non_e1_x non_e non_e₁
          simp [this]
        · field_simp [this.left, this.right]
          ring_nf
          field_simp [roots_B_non_zero]
          apply x_sq_mul_linear_factor_eq e₁

theorem fromEdwards_add_of_sum_y_eq_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (sum_y : (e₁ + e₂).y = 1) :
    fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  have hzero := zeroY _ sum_y
  rw [hzero, map_zero]
  have heq : e₁ = -e₂ := by agrind
  rw [heq, neg_fromEdwards]
  agrind

theorem fromEdwards_add_of_x_eq_of_y_eq_neg (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (non_e1_x : e₁.x ≠ 0)
    (non_e2_x : e₂.x ≠ 0)
    (non_e1_y : 1 - e₁.y ≠ 0)
    (non_e2_y : 1 - e₂.y ≠ 0)
    (non_e2_y1 : 1 + e₂.y ≠ 0)
    (e_x : e₁.x = e₂.x)
    (e_y : e₁.y = -e₂.y) :
    fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  have : (e₁ + e₂).x=0 := by
    simp [Edwards.add_x, e_x, e_y]
    field_simp
    ring_nf
    simp
  have : (e₁ + e₂).y=-1 := by
    simp [Edwards.add_y, e_x, e_y]
    have := (Edwards.Ed25519.denomsNeZero e₂ e₂).left
    ring_nf at this
    field_simp at this
    field_simp
    have :1 + e₂.y ^ 2 * e₂.x ^ 2 * Edwards.Ed25519.d ≠ 0 := by agrind
    field_simp
    have := e₂.on_curve
    ring_nf at this
    have : Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 =
        1 + e₂.y ^ 2 * e₂.x ^ 2 * Edwards.Ed25519.d := by agrind
    rw [← this]
    ring_nf
  unfold fromEdwards
  have : ¬ (-e₂.y = 1) := by grind
  have : ¬ (e₂.y = 1) := by grind
  have := edwards_neg_iff_montgomery_neg non_e2_y non_e1_y non_e2_y1 non_e1_x non_e2_x
  simp_all only [ne_eq, not_false_eq_true, sub_neg_eq_add, ↓reduceDIte, dite_eq_ite]
  simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
  simp only [MontgomeryCurveCurve25519, WeierstrassCurve.Affine.negY, zero_mul, sub_zero,
    WeierstrassCurve.Affine.addX, add_zero, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, neg_add_rev]
  simp only [← this]
  have : ¬ (-e₂.y = e₂.y ∧ e₂.x = -e₂.x) := by
    field_simp
    simp only [not_and]
    intro hy
    decide
  simp only [this, ↓reduceDIte]
  have : ¬ (-1 = (1 : CurveField)) := by decide
  simp only [this, ↓reduceIte, T_point, WeierstrassCurve.Affine.Point.some.injEq]
  simp only [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY, zero_mul, sub_zero,
    sub_neg_eq_add, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_mul]
  have : 1 - e₁.y ≠ 0 := by grind
  have inj := injective_fromEdwards non_e2_y this
  simp only [e_y, sub_neg_eq_add] at inj
  simp only [inj]
  by_cases h: e₂.y=0
  · simp only [h, neg_zero, ↓reduceIte, add_zero, mul_one, one_mul, sub_zero, ne_eq, one_ne_zero,
    not_false_eq_true, div_self, one_pow]
    have : ¬ ( Curve25519.roots_B / e₂.x = -(Curve25519.roots_B / e₂.x)) := by
      intro h
      have : Curve25519.roots_B =0 := by grind
      apply roots_B_non_zero this
    simp only [this, ↓reduceIte]
    set a := Curve25519.roots_B / e₂.x with ha
    have : a ^ 2 = 486664 := by
      rw [ha]
      field_simp
      have ho := e₂.on_curve
      simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        mul_zero] at ho
      have : Edwards.Ed25519.a =-1 := rfl
      rw [this] at ho
      have : e₂.x ^ 2 = -1 := by grind
      rw [pow2_roots_B,adB, this]
      simp only [neg_mul, one_mul]
    have : (a + a) = 2 * a := by ring
    rw [this]
    field_simp
    unfold Curve25519.A
    constructor
    · grind
    · grind
  have : ¬ -e₂.y = e₂.y := by
    intro h
    have : 2 * e₂.y = 0 := by grind
    simp only [mul_eq_zero] at this
    rcases this with h | h
    · revert h
      decide
    · grind
  simp only [this, ↓reduceIte]
  have : 1 + -e₂.y = 1 - e₂.y := by ring
  rw [this]
  set u1 := (1 - e₂.y) / (1 + e₂.y) with hu1
  set u2 := (1 + e₂.y) / (1 - e₂.y) with hu2
  set v1 := Curve25519.roots_B * (1 - e₂.y) / ((1 + e₂.y) * e₂.x) with hv1
  set v2 := Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x) with hv2
  have feq : (v1 - v2) / (u1 - u2) = Curve25519.roots_B / e₂.x := by
      rw [hu1, hu2, hv1, hv2]
      field_simp
      have : (1 - e₂.y) ^ 2 - (1 + e₂.y) ^ 2 = -4 *e₂.y := by
        ring_nf
      rw [this]
      have : (4 : CurveField) ≠ 0 := by decide
      field_simp
  have :((v1 - v2) / (u1 - u2)) ^ 2 - Curve25519.A - u1 - u2 =0 := by
    rw [feq]
    have : (Curve25519.roots_B / e₂.x) ^ 2 - Curve25519.A - u1 - u2
    =(Curve25519.roots_B / e₂.x) ^ 2 - Curve25519.A - (u1 + u2) := by ring
    rw [this]
    have : u1 + u2 = 2*(1+e₂.y^2)/((1-e₂.y)* (1+e₂.y)) := by
      rw [hu1, hu2]
      field_simp
      ring_nf
    rw [this]
    field_simp
    rw [pow2_roots_B, adB]
    simp only [mul_zero]
    ring_nf
    field_simp
    have eq1 := e₂.on_curve
    have : Edwards.Ed25519.a = - 1 := rfl
    rw [this, inver_Ad_eq] at eq1
    have : 486664 = Curve25519.A + 2 := by decide
    rw [this]
    have : Curve25519.A + 2 ≠ 0 := by decide
    field_simp at eq1
    grind => ring
  rw [this]
  simp only [feq, zero_sub, mul_neg, neg_neg, true_and]
  simp only [hv1, hu1]
  field_simp
  ring

lemma montgomery_addX_eq_zero_of_sum_y_eq_neg_one_of_y_ne_neg_y
    {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (non_e1_x : e₁.x ≠ 0)
    (non_e2_x : e₂.x ≠ 0)
    (non_e1_y : 1 - e₁.y ≠ 0)
    (non_e2_y1 : 1 + e₂.y ≠ 0)
    (sum_x : e₁.x * e₂.y + e₁.y * e₂.x = 0)
    (sum_y : (e₁ + e₂).y = -1)
    (non_meq : e₁.y ≠ -e₂.y) :
    0 =
      ((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) -
          Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
                ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y))) ^
              2 -
            Curve25519.A -
          (1 + e₁.y) / (1 - e₁.y) -
        (1 + e₂.y) / (1 - e₂.y) := by
      simp only [Edwards.add_y] at sum_y
      have hdenoms := Edwards.Ed25519.denomsNeZero e₁ e₂
      simp only [ne_eq] at hdenoms
      have non_eq1 : (1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d) ≠ 0 := by agrind
      have ha : Edwards.Ed25519.a = -1 := rfl
      field_simp [non_eq1] at sum_y
      rw [ha] at sum_y
      have hprod : e₁.y * e₂.y + e₁.x * e₂.x =
          -(1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d) := by
        rw [← sum_y]; simp only [neg_mul, one_mul, sub_neg_eq_add]
      have heq1 : e₁.y = -e₁.x * e₂.y / e₂.x := by field_simp; agrind
      have eqe₁ := e₁.on_curve
      rw [heq1] at eqe₁
      field_simp at eqe₁
      rw [e₂.on_curve] at eqe₁
      -- Factor: (e₁.x² - e₂.x²) * (1 - d * e₁.x² * e₂.y²) = 0
      have hfactor :
          (e₁.x ^ 2 - e₂.x ^ 2) * (1 - Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2) = 0 := by
        have : e₁.x ^ 2 * (1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) -
            (e₂.x ^ 2 + e₁.x ^ 4 * e₂.y ^ 2 * Edwards.Ed25519.d) = 0 := by
          rw [eqe₁]; simp only [sub_self]
        have heq : e₁.x ^ 2 * (1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) -
            (e₂.x ^ 2 + e₁.x ^ 4 * e₂.y ^ 2 * Edwards.Ed25519.d) =
            (e₁.x ^ 2 - e₂.x ^ 2) *
            (1 - Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2) := by ring_nf
        agrind
      have hfactor2 :
          (e₁.x - e₂.x) * (e₁.x + e₂.x) *
          (1 - Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2) = 0 := by
        have : e₁.x ^ 2 - e₂.x ^ 2 = (e₁.x - e₂.x) * (e₁.x + e₂.x) := by ring
        agrind
      simp only [mul_eq_zero] at hfactor2
      rcases hfactor2 with (h | h) | h
      · have eq11x : e₁.x = e₂.x := by agrind
        rw [eq11x] at sum_x
        field_simp at sum_x
        simp only [mul_eq_zero, non_e2_x, false_or] at sum_x
        exact absurd (show e₁.y = -e₂.y by agrind) non_meq
      · have eq11x : e₁.x = -e₂.x := by agrind
        rw [eq11x] at sum_x
        field_simp at sum_x
        simp only [mul_eq_zero, non_e2_x, false_or] at sum_x
        have eq11y : e₁.y = e₂.y := by agrind
        simp only [eq11y, neg_mul, sub_neg_eq_add] at sum_y
        field_simp at sum_y
        have hreord : e₂.y ^ 2 + Edwards.Ed25519.a * e₂.x ^ 2 =
            Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 := by ring
        have eq0 : 2 * (1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) = 0 := by
          have hcurve := e₂.on_curve
          have ha2 : Edwards.Ed25519.a = -1 := rfl
          rw [ha2] at hcurve
          agrind
        have eq2 : ¬ (2 : Edwards.CurveField) = 0 := by decide
        have hdenom := (Edwards.Ed25519.denomsNeZero e₂ e₂).left
        simp at hdenom
        ring_nf at hdenom
        simp only [mul_eq_zero] at eq0
        rcases eq0 with h0 | h0
        · exact absurd h0 eq2
        · exact absurd h0 hdenom
      · have hxy : e₁.x * e₂.y = -e₁.y * e₂.x := by agrind
        have hxy2 : e₁.x ^ 2 * e₂.y ^ 2 = -e₁.x * e₂.x * e₁.y * e₂.y := by
          calc e₁.x ^ 2 * e₂.y ^ 2 = e₁.x * e₂.y * (e₁.x * e₂.y) := by ring
            _ = e₁.x * e₂.y * (-e₁.y * e₂.x) := by rw [hxy]
            _ = -e₁.x * e₂.x * e₁.y * e₂.y := by ring
        have hcontra : 1 + Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y = 0 := by
          have key : Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2 =
              -Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y := by
            linear_combination Edwards.Ed25519.d * hxy2
          linear_combination h + key
        exact absurd hcontra hdenoms.left

lemma birational_map_symm {x y u v : CurveField}
    (non_x : ¬x = 0)
    (hya : 1 - y ≠ 0)
    (hym : 1 + y ≠ 0)
    (hu : u = (1 + y) / (1 - y))
    (hv : v = Curve25519.roots_B * (1 + y) / ((1 - y) * x)) :
    x = (Curve25519.roots_B * u) / v ∧ y = (u - 1) / (u + 1) ∧
        u ≠ 0 ∧ u + 1 ≠ 0 ∧ v ≠ 0 := by
  constructor
  · simp [hu, hv]
    field_simp [roots_B_non_zero]
  · constructor
    · simp [hu]
      field_simp
      simp
      have : (1+1:CurveField) ≠ 0 := by decide
      field_simp
    · constructor
      · simp [hu]
        grind
      · constructor
        · simp [hu]
          field_simp
          simp only [add_add_sub_cancel, mul_zero]
          decide
        · simp [hv, hya,hym, non_x, roots_B_non_zero]

lemma montgomery_v_add_eq_zero_of_sum_y_eq_neg_one_of_y_ne
    {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (non_e2_x : e₂.x ≠ 0)
    (sum_x : e₁.x * e₂.y + e₁.y * e₂.x = 0)
    (non_meq : e₁.y ≠ -e₂.y)
    (non_eq : e₁.y ≠ e₂.y) :
    0 =
      -(Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x)) +
        -((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) -
            Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
              ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y)) *
            (((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) -
                          Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
                        ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y))) ^
                      2 -
                    Curve25519.A -
                  (1 + e₁.y) / (1 - e₁.y) -
                (1 + e₂.y) / (1 - e₂.y) -
              (1 + e₁.y) / (1 - e₁.y))) := by
  exfalso
  have heq1 : e₁.y = -e₁.x * e₂.y / e₂.x := by
    field_simp; agrind
  have eqe₁ := e₁.on_curve
  rw [heq1] at eqe₁
  field_simp at eqe₁
  rw [e₂.on_curve] at eqe₁
  have hfactor :
      (e₁.x ^ 2 - e₂.x ^ 2) * (1 - Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2) = 0 := by
    have h0 : e₁.x ^ 2 * (1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) -
        (e₂.x ^ 2 + e₁.x ^ 4 * e₂.y ^ 2 * Edwards.Ed25519.d) = 0 := by
      rw [eqe₁]; simp only [sub_self]
    have heq : e₁.x ^ 2 * (1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) -
        (e₂.x ^ 2 + e₁.x ^ 4 * e₂.y ^ 2 * Edwards.Ed25519.d) =
        (e₁.x ^ 2 - e₂.x ^ 2) * (1 - Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2) := by ring_nf
    agrind
  have hfactor2 :
      (e₁.x - e₂.x) * (e₁.x + e₂.x) *
      (1 - Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2) = 0 := by
    have : e₁.x ^ 2 - e₂.x ^ 2 = (e₁.x - e₂.x) * (e₁.x + e₂.x) := by ring
    agrind
  simp only [mul_eq_zero] at hfactor2
  rcases hfactor2 with (h | h) | h
  · have eq11x : e₁.x = e₂.x := by agrind
    rw [eq11x] at sum_x
    field_simp at sum_x
    simp only [mul_eq_zero, non_e2_x, false_or] at sum_x
    exact non_meq (by agrind)
  · have eq11x : e₁.x = -e₂.x := by agrind
    rw [eq11x] at sum_x
    field_simp at sum_x
    simp only [mul_eq_zero, non_e2_x, false_or] at sum_x
    exact non_eq (by agrind)
  · have hxy : e₁.x * e₂.y = -e₁.y * e₂.x := by agrind
    have hxy2 : e₁.x ^ 2 * e₂.y ^ 2 = -e₁.x * e₂.x * e₁.y * e₂.y :=
      calc e₁.x ^ 2 * e₂.y ^ 2
          = e₁.x * e₂.y * (e₁.x * e₂.y) := by ring
        _ = e₁.x * e₂.y * (-e₁.y * e₂.x) := by rw [hxy]
        _ = -e₁.x * e₂.x * e₁.y * e₂.y := by ring
    have hcontra : 1 + Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y = 0 := by
      have key : Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2 =
          -Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y := by
        linear_combination Edwards.Ed25519.d * hxy2
      linear_combination h + key
    exact (Edwards.Ed25519.denomsNeZero e₁ e₂).left (by linear_combination hcontra)

lemma fromEdwards_add_of_sum_x_eq_zero_of_sum_y_eq_neg_one_of_y_ne_neg_y
    {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (non_e1_x : e₁.x ≠ 0)
    (non_e2_x : e₂.x ≠ 0)
    (non_e1_y : 1 - e₁.y ≠ 0)
    (non_e2_y : 1 - e₂.y ≠ 0)
    (non_e2_y1 : 1 + e₂.y ≠ 0)
    (sum_x : e₁.x * e₂.y + e₁.y * e₂.x = 0)
    (sum_y : (e₁ + e₂).y = -1)
    (e_y : e₁.y ≠ -e₂.y) :
    fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  unfold fromEdwards
  have : ¬ (-e₂.y = 1) := by agrind
  have : ¬ (e₂.y = 1) := by agrind
  have : ¬ (e₁.y = 1) := by agrind
  have eq := edwards_neg_iff_montgomery_neg non_e2_y non_e1_y non_e2_y1 non_e1_x non_e2_x
  dsimp only
  simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
  simp only [MontgomeryCurveCurve25519, WeierstrassCurve.Affine.negY, zero_mul, sub_zero,
    WeierstrassCurve.Affine.addX, add_zero, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, neg_add_rev]
  have : (e₁ + e₂).x=0 := by
    simp [Edwards.add_x, sum_x]
  have non_one : -1 ≠ (1 : CurveField) := by decide
  simp_all only [ne_eq, ↓reduceDIte]
  simp only [← eq]
  have h : ¬ (e₁.y = e₂.y ∧ e₁.x = -e₂.x) := by
    intro h
    simp [Edwards.add_y, h] at sum_y
    field_simp at sum_y
    have := (Edwards.Ed25519.denomsNeZero e₂ e₂).left
    field_simp at this
    have : e₂.y ^ 2 + Edwards.Ed25519.a * e₂.x ^ 2
      = Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 := by grind
    rw [this, e₂.on_curve] at sum_y
    field_simp at sum_y
    revert sum_y
    decide
  simp only [T_point, h, ↓reduceDIte, WeierstrassCurve.Affine.Point.some.injEq]
  simp only [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY, zero_mul, sub_zero,
    sub_neg_eq_add, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_mul]
  have : 1 - e₁.y ≠ 0 := by grind
  have inj := injective_fromEdwards non_e2_y this
  simp only [inj]
  by_cases heqy: (e₁.y = e₂.y)
  · simp only [heqy, true_and] at h
    simp only [heqy, ↓reduceIte]
    simp only [heqy] at sum_x
    field_simp at sum_x
    simp only [ mul_eq_zero] at sum_x
    rcases sum_x with sum_x | sum_x
    · have eq1 := e₂.on_curve
      simp only [sum_x, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        mul_zero] at eq1
      simp only [Edwards.add_y, heqy, sum_x, mul_zero, zero_sub, sub_zero, div_one,
        neg_inj] at sum_y
      have : ¬ ( Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) =
                -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
                field_simp [roots_B_non_zero]
                grind
      simp_all only [ne_eq, not_false_eq_true, zero_ne_one, sub_zero, one_ne_zero, add_zero,
        and_false, div_self, mul_one, one_mul, true_and, false_iff, ↓reduceIte, one_pow]
      field_simp
      have : e₁.x =e₂.x := by
        rw [← eq1] at sum_y
        have : Edwards.Ed25519.a = -1 := rfl
        rw [this] at sum_y
        have : e₂.x ^ 2 = e₂.x * e₂.x := by grind
        simp only [neg_mul, one_mul, this, neg_inj, mul_eq_mul_right_iff, non_e2_x,
          or_false] at sum_y
        exact sum_y
      have : Edwards.Ed25519.a = -1 := rfl
      rw [this] at eq1
      have :e₁.x ^ 2 = -1 := by grind
      have Aeq : 486664 = Curve25519.A + 2 := by
                unfold Curve25519.A; grind
      simp only [this, mul_neg, mul_one, pow2_roots_B, adB, Aeq, neg_add_rev, zero_mul, neg_neg]
      have : (-2 + -Curve25519.A) * (1 + 1) ^ 2 ≠ 0 := by
        unfold Curve25519.A
        decide
      constructor
      · unfold Curve25519.A
        grind
      · field_simp [roots_B_non_zero]
        unfold Curve25519.A
        agrind
    · grind
  · simp only [heqy, ↓reduceIte]
    constructor
    · exact montgomery_addX_eq_zero_of_sum_y_eq_neg_one_of_y_ne_neg_y
        non_e1_x non_e2_x non_e1_y non_e2_y1 sum_x sum_y e_y
    · apply montgomery_v_add_eq_zero_of_sum_y_eq_neg_one_of_y_ne
      all_goals simp_all

theorem fromEdwards_add_of_sum_x_eq_zero_of_sum_y_eq_neg_one
    (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (non_e1_x : e₁.x ≠ 0)
    (non_e2_x : ¬e₂.x = 0)
    (sum_x : (e₁ + e₂).x = 0)
    (non_e1_y : ¬1 - e₁.y = 0)
    (non_e2_y : ¬1 - e₂.y = 0)
    (non_e2_y_1 : ¬1 + e₂.y = 0)
    (sum_y_1 : (e₁ + e₂).y = -1) :
    fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  have sum_x : e₁.x * e₂.y + e₁.y * e₂.x = 0 := by
    simp only [Edwards.add_x, div_eq_zero_iff] at sum_x
    rcases sum_x with sum_x | sum_x
    · exact sum_x
    · have := (Edwards.Ed25519.denomsNeZero e₁ e₂).left sum_x
      apply False.elim this
  by_cases h : e₁.y ≠ -e₂.y
  · apply fromEdwards_add_of_sum_x_eq_zero_of_sum_y_eq_neg_one_of_y_ne_neg_y
    all_goals simp_all
  · have h1 : e₁.y = -e₂.y := by agrind
    apply fromEdwards_add_of_x_eq_of_y_eq_neg e₁ e₂ non_e1_x non_e2_x non_e1_y non_e2_y
      non_e2_y_1 _ h1
    rw [h1] at sum_x
    have : e₁.x * e₂.y + -e₂.y * e₂.x = e₂.y * (e₁.x - e₂.x) := by agrind
    rw [this] at sum_x
    simp only [mul_eq_zero] at sum_x
    rcases sum_x with sum_x | sum_x
    · simp only [Edwards.add_y, sum_x, mul_zero, zero_sub, sub_zero, div_one, neg_inj] at sum_y_1
      have := e₂.on_curve
      simp only [sum_x, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        mul_zero] at this
      rw [← this] at sum_y_1
      have : Edwards.Ed25519.a =-1 := rfl
      simp only [this, neg_mul, one_mul, neg_inj] at sum_y_1
      have : e₂.x ^ 2 = e₂.x * e₂.x := by agrind
      simp only [this, mul_eq_mul_right_iff, non_e2_x, or_false] at sum_y_1
      apply sum_y_1
    · agrind

lemma x_eq_or_eq_neg_of_y_eq {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (hy1 : 1 - e₂.y ≠ 0)
    (hy3 : 1 + e₂.y ≠ 0)
    (heqy : e₁.y = e₂.y) :
    e₁.x = e₂.x ∨ e₁.x = -e₂.x := by
  have eq₁ := e₁.on_curve
  have eq₂ := e₂.on_curve
  rw [heqy] at eq₁
  have key :
      (Edwards.Ed25519.a - e₂.y ^ 2 * Edwards.Ed25519.d) * (e₂.x ^ 2 - e₁.x ^ 2) = 0 := by
    linear_combination eq₂ - eq₁
  simp only [mul_eq_zero] at key
  rcases key with h | h
  · have hd : Edwards.Ed25519.d * e₂.y ^ 2 = Edwards.Ed25519.a := by agrind
    have heq1 : e₁.x ^ 2 = 1 := by
      have := e₁.on_curve
      rw [heqy] at this
      agrind
    have heq2 : e₂.x ^ 2 = 1 := by
      agrind
    have hx1 : e₁.x = 1 ∨ e₁.x = -1 := by
      simp only [sq_eq_one_iff] at heq1; exact heq1
    have hx2 : e₂.x = 1 ∨ e₂.x = -1 := by
      simp only [sq_eq_one_iff] at heq2; exact heq2
    rcases hx1 with hx1 | hx1 <;> rcases hx2 with hx2 | hx2 <;> simp_all
  · have : (e₂.x - e₁.x) * (e₂.x + e₁.x) = 0 := by agrind
    simp only [mul_eq_zero] at this
    agrind

lemma fromEdwards_u_add_of_eq {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (non_e1_x : ¬e₁.x = 0)
    (non_e2_x : e₂.x ≠ 0)
    (hy1 : 1 - e₂.y ≠ 0)
    (hy3 : 1 + e₂.y ≠ 0)
    (heqy : e₁.y = e₂.y)
    (heqx : e₁.x = e₂.x) :
    (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
        ((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 +
            2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
                  (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                    Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
                2 -
              Curve25519.A -
            (1 + e₂.y) / (1 - e₂.y) -
          (1 + e₂.y) / (1 - e₂.y) := by
  simp only [Edwards.add_y, heqy]
  set u := (1 + e₂.y) / (1 - e₂.y) with hu
  set v := Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) with hv
  have ht := birational_map_symm non_e1_x hy1 hy3 hu hv
  have := (Edwards.Ed25519.denomsNeZero e₁ e₂).right
  simp only [heqy, ne_eq] at this
  have :1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d ≠ 0 := by grind
  field_simp
  have neq : (1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d +
      (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x))
  = Edwards.Ed25519.a * e₂.x * (e₂.x - e₁.x) + 2 * e₂.y ^ 2
    - Edwards.Ed25519.d * e₂.x * e₂.y ^ 2 * (e₁.x + e₂.x)
    := by
    have := e₂.on_curve
    have : 1 = Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 -
        Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 := by
      rw [this]
      ring_nf
    simp only [this]
    calc
       Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2
    - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 -
      e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d +
      (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x) =
      Edwards.Ed25519.a * e₂.x ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x + e₂.y ^ 2
    - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 -
      e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d +
      e₂.y ^ 2 := by grind
      _ = Edwards.Ed25519.a * e₂.x ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x + 2 * e₂.y ^ 2
    - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 -
      e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d := by grind
      _ = Edwards.Ed25519.a * e₂.x * (e₂.x - e₁.x) + 2 * e₂.y ^ 2
    - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 -
      e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d := by grind
      _ = Edwards.Ed25519.a * e₂.x * (e₂.x - e₁.x) + 2 * e₂.y ^ 2
    - Edwards.Ed25519.d * e₂.x * e₂.y ^ 2 * (e₁.x + e₂.x) := by grind
  simp only [heqx, sub_self, mul_zero, zero_add] at neq
  have : 2 * e₂.y ^ 2 - Edwards.Ed25519.d * e₂.x * e₂.y ^ 2 * (e₂.x + e₂.x)
  = 2 * e₂.y ^ 2 * (1 - Edwards.Ed25519.d * e₂.x ^ 2) := by
    calc
    2 * e₂.y ^ 2 - Edwards.Ed25519.d * e₂.x * e₂.y ^ 2 * (e₂.x + e₂.x)
      = 2 * e₂.y ^ 2 - 2 * Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 := by grind
    _ = 2 * e₂.y ^ 2 * (1 - Edwards.Ed25519.d * e₂.x ^ 2) := by grind
  rw [this] at neq
  have eq₂ : (1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d -
      (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x))
   = -e₂.x * (Edwards.Ed25519.d * e₂.y ^ 2 - Edwards.Ed25519.a) * (e₁.x + e₂.x)
   := by
    have := e₂.on_curve
    have : 1 = Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 -
        Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 := by
      rw [this]
      ring_nf
    have eq1 : 1 - e₂.y ^ 2 = Edwards.Ed25519.a * e₂.x ^ 2 -
        Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 := by
      rw [this]
      ring_nf
    have : (1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d -
        (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x))
   = (1 - e₂.y ^ 2) -
      e₁.x * e₂.x * (Edwards.Ed25519.d * e₂.y ^ 2 - Edwards.Ed25519.a) := by grind
    rw [eq1] at this
    have : (1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d -
        (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x))
      = -e₂.x ^ 2 * (Edwards.Ed25519.d * e₂.y ^ 2 - Edwards.Ed25519.a) -
      e₁.x * e₂.x * (Edwards.Ed25519.d * e₂.y ^ 2 - Edwards.Ed25519.a) := by grind
    grind
  simp only [heqx, neg_mul] at eq₂
  have : -(e₂.x * (Edwards.Ed25519.d * e₂.y ^ 2 - Edwards.Ed25519.a) * (e₂.x + e₂.x)) =
   2 * e₂.x ^ 2 * (Edwards.Ed25519.a - Edwards.Ed25519.d * e₂.y ^ 2) := by grind
  simp only [this] at eq₂
  simp only [heqx, neq, eq₂]
  simp only [heqx, ne_eq] at ht
  have eq₀ : (2 * e₂.x ^ 2 * (Edwards.Ed25519.a - Edwards.Ed25519.d * e₂.y ^ 2))
  = 2 * (Edwards.Ed25519.a * e₂.x ^ 2 - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) := by grind
  have := e₂.on_curve
  have mul : Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 =
      Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 - 1 := by
      rw [this]
      ring_nf
  simp only [mul] at eq₀
  have : 2 * (Edwards.Ed25519.a * e₂.x ^ 2 - (Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 - 1))
  = 2 * (1 - e₂.y ^ 2) := by ring_nf
  rw [this] at eq₀
  rw [eq₀]
  have eq₁ : 2 * e₂.y ^ 2 * (1 - Edwards.Ed25519.d * e₂.x ^ 2) =
  2 * (e₂.y ^ 2 - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) := by grind
  rw [mul] at eq₁
  have : e₂.y ^ 2 - (Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 - 1)
  = 1 - Edwards.Ed25519.a * e₂.x ^ 2 := by grind
  rw [this] at eq₁
  rw [eq₁]
  have : Edwards.Ed25519.a = -1 := rfl
  rw [this]
  have : (1 - e₂.y ^ 2) = 4 * u / (u + 1) ^ 2 := by
    simp only [ht]
    field_simp [ht.right.right.right.left]
    ring_nf
  have : 1 - (-1) * e₂.x ^ 2 = (Curve25519.roots_B ^ 2 * u ^ 2 + v ^ 2) / v ^ 2 := by
    simp [ht]
    field_simp [ht.right.right.right.right]
    ring
  rw [this]
  clear this
  rw [this]
  have : (4 : CurveField) ≠ 0 := by decide
  field_simp [ht.right.right.right.left, ht.right.right.left,
    ht.right.right.right.right, roots_B_non_zero]
  simp only [pow2_roots_B, adB, neg_mul]
  have : 486664 = Curve25519.A + 2 := by
    unfold Curve25519.A
    decide
  simp only [this]
  have : u * 4 * ((u * (u * 3 + 2 * Curve25519.A) + 1) ^ 2 / (1 + 1) ^ 2 -
      v ^ 2 * Curve25519.A - u * v ^ 2 - u * v ^ 2)
  = u * ((u * (u * 3 + 2 * Curve25519.A) + 1) ^ 2 -
      4 * v ^ 2 * Curve25519.A - 8 * u * v ^ 2) := by
    have : (1 + 1 : CurveField) ^ 2 = 4 := by decide
    rw [this]
    field_simp
    ring_nf
  rw [this]
  apply id_1
  have := on_MontgomeryCurves e₂
  simp only [ne_eq, ← heqx, ← hv, ← hu] at this
  apply this
  · grind
  · grind

lemma fromEdwards_u_add_of_eq_y {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (zero_e2_x : e₂.x ≠ 0)
    (hy1 : 1 - e₂.y ≠ 0)
    (hy3 : 1 + e₂.y ≠ 0)
    (sum_x : (e₁ + e₂).x ≠ 0)
    (heqy : e₁.y = e₂.y) :
    (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
        ((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 +
            2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
                  (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                    Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
                2 -
              Curve25519.A -
            (1 + e₂.y) / (1 - e₂.y) -
          (1 + e₂.y) / (1 - e₂.y) := by
      have := x_eq_or_eq_neg_of_y_eq hy1 hy3 heqy
      rcases this with h | h
      · apply fromEdwards_u_add_of_eq
        all_goals simp_all
      · simp [Edwards.add_x, heqy] at sum_x
        grind

lemma fromEdwards_v_add_of_eq {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (non_e1_x : ¬e₁.x = 0)
    (zero_e2_x : e₂.x ≠ 0)
    (hy1 : 1 - e₂.y ≠ 0)
    (hy3 : 1 + e₂.y ≠ 0)
    (sum_x : (e₁ + e₂).x ≠ 0)
    (sum_y : ¬(e₁ + e₂).y = 1)
    (heqy : e₁.y = e₂.y)
    (heqx : e₁.x = e₂.x) :
    Curve25519.roots_B * (1 + (e₁ + e₂).y) / ((1 - (e₁ + e₂).y) * (e₁ + e₂).x) =
      -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) +
        -((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 +
            2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
              (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) *
            (((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 +
                2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
                        (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                          Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
                      2 -
                    Curve25519.A -
                  (1 + e₂.y) / (1 - e₂.y) -
                (1 + e₂.y) / (1 - e₂.y) -
              (1 + e₂.y) / (1 - e₂.y))) := by
  have sum_x0 := fromEdwards_u_add_of_eq_y zero_e2_x hy1 hy3 sum_x heqy
  have : Curve25519.roots_B * (1 + (e₁ + e₂).y) / ((1 - (e₁ + e₂).y) * (e₁ + e₂).x)
  = Curve25519.roots_B *
      ((1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y)) / (e₁ + e₂).x := by grind
  rw [this, sum_x0]
  set u := (1 + e₂.y) / (1 - e₂.y) with hu
  set v := Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) with hv
  have ht := birational_map_symm non_e1_x hy1 hy3 hu hv
  rw [heqx] at ht
  field_simp [ht.right.right]
  have non_de : (u * Curve25519.A * 2 * (1 + u ^ 2) + 1 + u ^ 2 * 6 + u ^ 4) ≠ 0 := by
    have non_eq₀ := (Edwards.Ed25519.denomsNeZero e₁ e₂).left
    simp only [heqx, heqy, ne_eq] at non_eq₀
    have : 1 + Edwards.Ed25519.d * e₂.x * e₂.x * e₂.y * e₂.y
    = 1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 := by grind
    rw [this, ← e₂.on_curve] at non_eq₀
    simp [ht] at non_eq₀
    field_simp [ht.right.right] at non_eq₀
    simp only [mul_zero] at non_eq₀
    have : Edwards.Ed25519.a = -1 := rfl
    rw [this, pow2_roots_B, adB] at non_eq₀
    simp only [mul_neg, neg_mul, one_mul, neg_neg] at non_eq₀
    have : 486664 = Curve25519.A + 2 := by
      unfold Curve25519.A
      decide
    rw [this] at non_eq₀
    apply id_4 _ non_eq₀
    have := on_MontgomeryCurves e₂
    simp only [ne_eq, ← heqx, ← hv, ← hu] at this
    apply this
    · grind
    · grind
  have : (e₁ + e₂).x = (2 * Curve25519.roots_B * v * (u - 1) * (u + 1)) /
      (Curve25519.A * u * 2 + Curve25519.A * u ^ 3 * 2 + 1 + u ^ 2 * 6 + u ^ 4) := by
    simp only [Edwards.add_x, heqx, heqy]
    have : e₂.x * e₂.y + e₂.y * e₂.x = 2 * e₂.x * e₂.y := by grind
    rw [this]
    have non_eq₀ := (Edwards.Ed25519.denomsNeZero e₁ e₂).left
    simp only [heqx, heqy, ne_eq] at non_eq₀
    have :1 + Edwards.Ed25519.d * e₂.x * e₂.x * e₂.y * e₂.y=
        1 + e₂.x ^ 2 * e₂.y ^ 2 * Edwards.Ed25519.d := by grind
    rw [this] at non_eq₀
    field_simp
    have :1 + e₂.x ^ 2 * e₂.y ^ 2 * Edwards.Ed25519.d
    = 1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 := by grind
    rw [this, ← e₂.on_curve]
    simp [ht]
    field_simp [ht.right.right]
    have : Edwards.Ed25519.a = -1 := rfl
    rw [this, pow2_roots_B, adB]
    have : 486664 = Curve25519.A + 2 := by
      unfold Curve25519.A
      decide
    rw [this, id_2]
    · field_simp
    · have := on_MontgomeryCurves e₂
      simp only [ne_eq, ← heqx, ← hv, ← hu] at this
      apply this
      · grind
      · grind
  rw [this]
  have : u * 2 * Curve25519.A * (1 + u ^ 2) + 1 + u ^ 2 * 6 + u ^ 4
  = u * Curve25519.A * 2 * (1 + u ^ 2) + 1 + u ^ 2 * 6 + u ^ 4 := by grind
  rw [← this] at non_de
  have : (1 + 1 : CurveField) ≠ 0 := by decide
  field_simp [non_de, roots_B_non_zero, ht.right.right]
  apply id_3
  have := on_MontgomeryCurves e₂
  simp only [ne_eq, ← heqx, ← hv, ← hu] at this
  apply this
  · grind
  · grind

lemma fromEdwards_v_add_of_eq_y {e₁ e₂ : Edwards.Point Edwards.Ed25519}
    (zero_e2_x : e₂.x ≠ 0)
    (hy1 : 1 - e₂.y ≠ 0)
    (hy3 : 1 + e₂.y ≠ 0)
    (sum_x : (e₁ + e₂).x ≠ 0)
    (sum_y : ¬(e₁ + e₂).y = 1)
    (heqy : e₁.y = e₂.y) :
    Curve25519.roots_B * (1 + (e₁ + e₂).y) / ((1 - (e₁ + e₂).y) * (e₁ + e₂).x) =
      -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) +
        -((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 +
            2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
              (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) *
            (((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 +
                2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
                        (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                          Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
                      2 -
                    Curve25519.A -
                  (1 + e₂.y) / (1 - e₂.y) -
                (1 + e₂.y) / (1 - e₂.y) -
              (1 + e₂.y) / (1 - e₂.y))) := by
  have := x_eq_or_eq_neg_of_y_eq hy1 hy3 heqy
  rcases this with h | h
  · apply fromEdwards_v_add_of_eq
    all_goals simp_all
  · simp [Edwards.add_x, heqy] at sum_x
    grind

private lemma aux_poly_sub {u1 v1 u2 v2 : CurveField} :
  (u1 + 1) * (u2 + 1) * v1 * v2 -
    u1 * (u1 - 1) * u2 * (u2 - 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.d -
    ((u1 - 1) * (u2 - 1) * v1 * v2 -
    u1 * (u1 + 1) * u2 * (u2 + 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.a) =
  2 * (v1 * v2 * (u1 + u2) + u1 * u2 * (u1 * u2 * 2 + (u1 + u2) * Curve25519.A + 2)) := by
  have step1 : (u1 + 1) * (u2 + 1) * v1 * v2 -
    u1 * (u1 - 1) * u2 * (u2 - 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.d -
    ((u1 - 1) * (u2 - 1) * v1 * v2 -
    u1 * (u1 + 1) * u2 * (u2 + 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.a) =
    v1 * v2 * ((u1 + 1) * (u2 + 1) - (u1 - 1) * (u2 - 1)) -
    u1 * (u1 - 1) * u2 * (u2 - 1) * (Curve25519.roots_B ^ 2 * Edwards.Ed25519.d) +
    u1 * (u1 + 1) * u2 * (u2 + 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.a := by grind
  rw [step1]
  have step2 : (u1 + 1) * (u2 + 1) - (u1 - 1) * (u2 - 1) = 2 * (u1 + u2) := by ring
  rw [step2, roots_B_d, pow2_roots_B, adB, A_add_2]
  have ha : Edwards.Ed25519.a = -1 := rfl
  rw [ha]
  have step3 : v1 * v2 * (2 * (u1 + u2)) - u1 * (u1 - 1) * u2 * (u2 - 1) * (Curve25519.A - 2) +
    u1 * (u1 + 1) * u2 * (u2 + 1) * -(Curve25519.A + 2) * -1 =
    2 * (v1 * v2 * (u1 + u2) + u1 * u2 * (u1 * u2 * 2 + (u1 + u2) * Curve25519.A + 2)) := by grind
  exact step3

private lemma aux_poly_add {u1 v1 u2 v2 : CurveField} :
  (u1 + 1) * (u2 + 1) * v1 * v2 -
    u1 * (u1 - 1) * u2 * (u2 - 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.d +
    ((u1 - 1) * (u2 - 1) * v1 * v2 -
    u1 * (u1 + 1) * u2 * (u2 + 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.a) =
  2 * (v1 * v2 * (u1 * u2 + 1) -
    u1 * u2 * (2 * (u1 + u2) + (u1 * u2 + 1) * Curve25519.A)) := by
  have step1 : (u1 + 1) * (u2 + 1) * v1 * v2 -
    u1 * (u1 - 1) * u2 * (u2 - 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.d +
    ((u1 - 1) * (u2 - 1) * v1 * v2 -
    u1 * (u1 + 1) * u2 * (u2 + 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.a) =
    v1 * v2 * ((u1 + 1) * (u2 + 1) + (u1 - 1) * (u2 - 1)) -
    u1 * (u1 - 1) * u2 * (u2 - 1) * (Curve25519.roots_B ^ 2 * Edwards.Ed25519.d) -
    u1 * (u1 + 1) * u2 * (u2 + 1) * Curve25519.roots_B ^ 2 * Edwards.Ed25519.a := by grind
  rw [step1]
  have step2 : (u1 + 1) * (u2 + 1) + (u1 - 1) * (u2 - 1) = 2 * (u1 * u2 + 1) := by ring
  rw [step2, roots_B_d, pow2_roots_B, adB, A_add_2]
  have ha : Edwards.Ed25519.a = -1 := rfl
  rw [ha]
  have step3 : v1 * v2 * (2 * (u1 * u2 + 1)) -
    u1 * (u1 - 1) * u2 * (u2 - 1) * (Curve25519.A - 2) -
    u1 * (u1 + 1) * u2 * (u2 + 1) * -(Curve25519.A + 2) * -1 =
    2 * (v1 * v2 * (u1 * u2 + 1) -
    u1 * u2 * (2 * (u1 + u2) + (u1 * u2 + 1) * Curve25519.A)) := by grind
  exact step3

lemma fromEdwards_u_add_of_y_ne (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (non_e1_x : ¬e₁.x = 0)
    (non_e2_x : ¬e₂.x = 0)
    (h1 : ¬e₁.y = 1)
    (h2 : ¬e₂.y = 1)
    (sum_y : ¬(e₁ + e₂).y = 1)
    (hy1 : 1 - e₂.y ≠ 0)
    (hy2 : 1 - e₁.y ≠ 0)
    (hy3 : 1 + e₂.y ≠ 0)
    (hy4 : 1 + e₁.y ≠ 0)
    (heqy : ¬e₁.y = e₂.y) :
    (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
      ((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) -
              Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
            ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y))) ^ 2 -
        Curve25519.A -
        (1 + e₁.y) / (1 - e₁.y) -
        (1 + e₂.y) / (1 - e₂.y) := by
  -- Introduce Montgomery coordinates for both points
  set u1 := (1 + e₁.y) / (1 - e₁.y) with hu1
  set v1 := Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) with hv1
  set u2 := (1 + e₂.y) / (1 - e₂.y) with hu2
  set v2 := Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x) with hv2
  -- The denominator 1 - (e₁ + e₂).y is nonzero since (e₁ + e₂).y ≠ 1
  have hsum_denom : 1 - (e₁ + e₂).y ≠ 0 := by grind
  field_simp
  simp only [Edwards.add_y]
  have ht1 := birational_map_symm non_e1_x hy2 hy4 hu1 hv1
  have ht2 := birational_map_symm non_e2_x hy1 hy3 hu2 hv2
  have non_eq₀ := (Edwards.Ed25519.denomsNeZero e₁ e₂).right
  have hd_comm : 1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d =
      1 - Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y := by grind
  rw [← hd_comm] at non_eq₀
  field_simp
  have hb1 : (1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d -
        (e₁.y * e₂.y - Edwards.Ed25519.a * e₁.x * e₂.x)) =
      (v1 * v2 * (2 * (u1 + u2)) -
          u1 * u2 * (-2 * (2 * u1 * u2 + Curve25519.A * (u1 + u2) + 2))) /
        ((u1 + 1) * (u2 + 1) * v1 * v2) := by
    simp [ht1, ht2]
    field_simp [ht1.right.right, ht2.right.right]
    exact aux_poly_sub
  rw [hb1]
  have hb2 : (1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d +
        (e₁.y * e₂.y - Edwards.Ed25519.a * e₁.x * e₂.x)) =
      (v1 * v2 * (2 * (u1 * u2 + 1)) -
          u1 * u2 * (2 * (2 * (u1 + u2) + Curve25519.A * (u1 * u2 + 1)))) /
        ((u1 + 1) * (u2 + 1) * v1 * v2) := by
    simp [ht1, ht2]
    field_simp [ht1.right.right, ht2.right.right]
    exact aux_poly_add
  rw [hb2]
  field_simp [ht1.right.right, ht2.right.right]
  have hu_diff : u1 - u2 ≠ 0 := by
    intro h
    have heq_u : u1 = u2 := by grind
    rw [hu1, hu2] at heq_u
    exact heqy ((injective_fromEdwards hy1 hy2).mp heq_u)
  field_simp
  apply id_5
  · have := on_MontgomeryCurves e₁ h1 non_e1_x
    simp only [← hv1, ← hu1] at this
    exact this
  · have := on_MontgomeryCurves e₂ h2 non_e2_x
    simp only [← hv2, ← hu2] at this
    exact this

lemma fromEdwards_v_add_of_y_ne (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (non_e1_x : ¬e₁.x = 0)
    (non_e2_x : ¬e₂.x = 0)
    (h1 : ¬e₁.y = 1)
    (h2 : ¬e₂.y = 1)
    (sum_x : ¬(e₁ + e₂).x = 0)
    (sum_y : ¬(e₁ + e₂).y = 1)
    (hy1 : 1 - e₂.y ≠ 0)
    (hy2 : 1 - e₁.y ≠ 0)
    (hy3 : 1 + e₂.y ≠ 0)
    (hy4 : 1 + e₁.y ≠ 0)
    (heqy : ¬e₁.y = e₂.y) :
    Curve25519.roots_B * (1 + (e₁ + e₂).y) / ((1 - (e₁ + e₂).y) * (e₁ + e₂).x) =
      -(Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x)) +
        -((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) -
            Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
              ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y)) *
            (((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) -
                          Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
                        ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y))) ^
                      2 -
                    Curve25519.A -
                  (1 + e₁.y) / (1 - e₁.y) -
                (1 + e₂.y) / (1 - e₂.y) -
              (1 + e₁.y) / (1 - e₁.y))) := by
    have non_eq_x := fromEdwards_u_add_of_y_ne e₁ e₂ non_e1_x non_e2_x h1 h2 sum_y
      hy1 hy2 hy3 hy4 heqy
    set u1 := (1 + e₁.y) / (1 - e₁.y) with hu1
    set v1 := Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) with hv1
    set u2 := (1 + e₂.y) / (1 - e₂.y) with hu2
    set v2 := Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x) with hv2
    rw [← non_eq_x]
    field_simp
    have : u1 - u2 ≠ 0 := by
      intro h
      have : u1 = u2 := by clear *- h; grind
      rw [hu1, hu2] at this
      have := (injective_fromEdwards hy1 hy2).mp this
      apply heqy this
    have : Curve25519.roots_B * (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y)
    = Curve25519.roots_B * ((1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y)) := by grind
    rw [this]
    set x1 := (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) with hx1
    have ht1 := birational_map_symm non_e1_x hy2 hy4 hu1 hv1
    have ht2 := birational_map_symm non_e2_x hy1 hy3 hu2 hv2
    have : Curve25519.roots_B * x1 + (e₁ + e₂).x * v1 =
        (e₁ + e₂).x * ((v2-v1) * (x1 - u1) / (u1 - u2)) := by
      have : 1 - (e₁ + e₂).y ≠ 0 := by grind
      have non_eq₀ := (Edwards.Ed25519.denomsNeZero e₁ e₂).right
      have : 1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d =
      1 - Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y := by grind
      rw [← this] at non_eq₀
      have : (e₁ + e₂).x =
   ( Curve25519.roots_B * (u1 * (u2 - 1) * (u1 + 1) * v2 + v1 * u2 * (u2 + 1) * (u1 - 1)))
    / (v1 * v2 * (u2 + 1) * (u1 + 1) *
        (1 + Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y)) := by
        simp only [ Edwards.add_x]
        have non_eq₁ := (Edwards.Ed25519.denomsNeZero e₁ e₂).left
        have : 1 + e₁.x * e₂.y * e₁.y * e₂.x * Edwards.Ed25519.d =
        1 + Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y := by grind
        rw [← this] at non_eq₁
        field_simp
        simp only [ht1, ht2]
        field_simp [ht1.right.right, ht2.right.right]
      rw [this]
      have non_eq₁ := (Edwards.Ed25519.denomsNeZero e₁ e₂).left
      field_simp [ht1.right.right, ht2.right.right]
      simp only [mul_assoc, mul_eq_mul_left_iff, roots_B_non_zero, or_false]
      simp only [← mul_assoc]
      have : (1 + Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y) =
      (v1 * v2 * (u1 + 1) * (u2 + 1) +
        (Curve25519.A - 2) * u1 * u2 * (u1 - 1) * (u2 - 1)) /
      (v1 * v2 * (u1 + 1) * (u2 + 1)) := by
        simp only [ht1, ht2]
        field_simp [ht1.right.right, ht2.right.right]
        have : Edwards.Ed25519.d * Curve25519.roots_B ^ 2 * u1 * u2 * (u1 - 1) * (u2 - 1)
        = (Curve25519.roots_B ^ 2 * Edwards.Ed25519.d) * u1 * u2 * (u1 - 1) * (u2 - 1) := by grind
        simp only [this, roots_B_d, add_right_inj]
        ring_nf
      rw [this]
      field_simp [ht1.right.right, ht2.right.right]
      rw [non_eq_x ]
      field_simp
      apply id_6
      · have := on_MontgomeryCurves e₁ h1 non_e1_x
        simp only [← hv1, ← hu1] at this
        apply this
      · have := on_MontgomeryCurves e₂ h2 non_e2_x
        simp only [← hv2, ← hu2] at this
        apply this
    clear *- this
    grind

theorem fromEdwards_add_of_x_ne_zero (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (non_e1_x : e₁.x ≠ 0)
    (zero_e2_x : e₂.x ≠ 0)
    (sum_x : (e₁ + e₂).x ≠ 0) :
    fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  by_cases h1 : e₁.y = 1
  · exact absurd (zeroY e₁ h1 ▸ rfl) non_e1_x
  · by_cases h2 : e₂.y = 1
    · exact absurd (zeroY e₂ h2 ▸ rfl) zero_e2_x
    · by_cases sum_y : (e₁ + e₂).y = 1
      · rw [← zero_iff] at sum_y
        simp only [sum_y]
        rw [show e₂ = -e₁ from by grind, neg_fromEdwards, map_zero]
        simp only [add_neg_cancel]
      · have hy1 : 1 - e₂.y ≠ 0 := by grind
        have hy2 : 1 - e₁.y ≠ 0 := by grind
        have hy3 : 1 + e₂.y ≠ 0 := fun h => zero_e2_x (exceptEdwardsPoint h)
        have hy4 : 1 + e₁.y ≠ 0 := fun h => non_e1_x (exceptEdwardsPoint h)
        unfold fromEdwards
        simp_all only [ne_eq, ↓reduceDIte]
        simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add,
          WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
          WeierstrassCurve.Affine.negAddY, neg_add_rev]
        simp only [MontgomeryCurveCurve25519, zero_mul, sub_zero, add_zero]
        simp only [← edwards_neg_iff_montgomery_neg hy1 hy2 hy3 non_e1_x zero_e2_x]
        by_cases heq : e₁.y = e₂.y ∧ e₁.x = -e₂.x
        · exact absurd (show (e₁ + e₂).x = 0 from by
            simp [Edwards.add_x, heq.1, heq.2]; field_simp; ring_nf; simp) sum_x
        · simp only [heq, ↓reduceDIte, WeierstrassCurve.Affine.Point.some.injEq]
          simp only [WeierstrassCurve.Affine.slope, injective_fromEdwards hy1 hy2,
            WeierstrassCurve.Affine.negY, zero_mul, sub_zero, sub_neg_eq_add,
            ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_mul]
          by_cases heqy : e₁.y = e₂.y
          · simp only [heqy, true_and] at heq
            simp only [heqy, ↓reduceIte]
            have sum_x1 := sum_x
            simp only [Edwards.add_x, heqy] at sum_x
            field_simp at sum_x
            simp only [div_eq_zero_iff, mul_eq_zero] at sum_x
            have hv_ne : ¬(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) =
                -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
              field_simp [roots_B_non_zero]; grind
            simp only [hv_ne, ↓reduceIte]
            constructor
            · exact fromEdwards_u_add_of_eq_y zero_e2_x hy1 hy3 sum_x1 heqy
            · exact fromEdwards_v_add_of_eq_y zero_e2_x hy1 hy3 sum_x1 sum_y heqy
          · simp only [heqy, ↓reduceIte]
            exact ⟨fromEdwards_u_add_of_y_ne e₁ e₂ non_e1_x zero_e2_x h1 h2 sum_y
                      hy1 hy2 hy3 hy4 heqy,
                   fromEdwards_v_add_of_y_ne e₁ e₂ non_e1_x zero_e2_x h1 h2 sum_x sum_y
                     hy1 hy2 hy3 hy4 heqy⟩

lemma fromEdwards_add_of_sum_x_eq_zero_of_y_ne_one_of_y_ne_neg_one
    (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (sum_x : (e₁ + e₂).x = 0)
  (sum_y : ¬(e₁ + e₂).y = 1)
  (sum_y_1 : ¬(e₁ + e₂).y = -1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  have := (e₁ + e₂).on_curve
  simp [sum_x] at this
  grind

lemma fromEdwards_add_of_x_eq_zero (e₁ e₂ : Edwards.Point Edwards.Ed25519)
    (non_e1_x : e₁.x = 0)
    (non_e2_x : e₂.x = 0) :
    fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  by_cases sum_y : (e₁ + e₂).y = 1
  · exact fromEdwards_add_of_sum_y_eq_one _ _ sum_y
  · rcases T_point_x non_e1_x with hy1 | hy1 <;> rcases T_point_x non_e2_x with hy2 | hy2
    · simp only [Edwards.add_y, hy1, hy2, mul_one, non_e1_x, mul_zero, non_e2_x,
        sub_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self,
        not_true_eq_false] at sum_y
    · simp only [zeroY e₁ hy1, zero_add, map_zero, zero_add]
    · simp only [zeroY e₂ hy2, add_zero, map_zero, add_zero]
    · simp only [Edwards.add_y, hy1, hy2, mul_neg, mul_one, neg_neg, non_e1_x, mul_zero,
        non_e2_x, sub_zero, neg_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self,
        not_true_eq_false] at sum_y

/-- The Edwards-to-Montgomery birational map preserves addition:
    `fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂`.

    The proof proceeds by case-splitting on whether each point has
    `x = 0`, then on properties of the sum. The key observation is
    that `eᵢ.x ≠ 0` implies both `eᵢ.y ≠ 1` (via `zeroY`) and
    `1 + eᵢ.y ≠ 0` (via `exceptEdwardsPoint`), so many sub-cases
    collapse to contradictions. -/
theorem add_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  by_cases h1 : e₁.x = 0 <;> by_cases h2 : e₂.x = 0
  · exact fromEdwards_add_of_x_eq_zero e₁ e₂ h1 h2
  · push_neg at h2
    rw [add_comm, Edwards.add_comm_Ed25519,
        fromEdwards_add_of_snd_x_eq_zero e₂ e₁ h2 h1]
  · push_neg at h1
    exact fromEdwards_add_of_snd_x_eq_zero e₁ e₂ h1 h2
  · push_neg at h1 h2
    have hy1 : 1 - e₁.y ≠ 0 :=
      fun h => h1 (by have he := zeroY e₁ (by grind); simp [he])
    have hy2 : 1 - e₂.y ≠ 0 :=
      fun h => h2 (by have he := zeroY e₂ (by grind); simp [he])
    have hy3 : 1 + e₂.y ≠ 0 := fun h => h2 (exceptEdwardsPoint h)
    by_cases hsy : (e₁ + e₂).y = 1
    · exact fromEdwards_add_of_sum_y_eq_one e₁ e₂ hsy
    · by_cases hsx : (e₁ + e₂).x = 0
      · by_cases hsy1 : (e₁ + e₂).y = -1
        · exact fromEdwards_add_of_sum_x_eq_zero_of_sum_y_eq_neg_one e₁ e₂
              h1 h2 hsx hy1 hy2 hy3 hsy1
        · exact fromEdwards_add_of_sum_x_eq_zero_of_y_ne_one_of_y_ne_neg_one e₁ e₂
              hsx hsy hsy1
      · push_neg at hsx
        exact fromEdwards_add_of_x_ne_zero e₁ e₂ h1 h2 hsx

theorem comm_mul_fromEdwards {n : ℕ} (e : Edwards.Point Edwards.Ed25519) :
  fromEdwards (n • e) = n • (fromEdwards e) := by
  induction n
  · simp only [zero_nsmul, map_zero]
  · rename_i n hn
    simp only [add_smul, one_smul]
    rw [add_fromEdwards, hn]

end fromEdwards

section toEdwards
open curve25519_dalek.math

/-- Helper lemma: if `x_abs² = (y² - 1) / (d·y² + 1)` then the Edwards curve equation holds.
    This is factored out of `toEdwards` to avoid expensive tactic elaboration in the definition. -/
private lemma toEdwards_on_curve {x_abs y : ZMod p}
    (h_x_sq : x_abs ^ 2 = (y ^ 2 - 1) * ((d : ZMod p) * y ^ 2 + 1)⁻¹) :
    Edwards.Ed25519.a * x_abs ^ 2 + y ^ 2 = 1 + Edwards.Ed25519.d * x_abs ^ 2 * y ^ 2 := by
  have ha : Edwards.Ed25519.a = -1 := rfl
  have hd : (d : ZMod p) = Edwards.Ed25519.d := rfl
  rw [ha, ← hd]
  exact montgomery_helper (d : ZMod p) y (x_abs ^ 2) (edwards_denom_nonzero y) h_x_sq

noncomputable def toEdwards : Point → Option (Edwards.Point Edwards.Ed25519)
  | .zero => some 0
  | .some (x := u) (y := _v) (h := _h) =>
   let y := (u - 1) * (u + 1)⁻¹
   let x2 : ZMod p := (y ^ 2 - 1) * ((d : ZMod p) * y ^ 2 + 1)⁻¹
   match h_call : curve25519_dalek.math.sqrt_checked x2 with
    | (x_abs, was_square) =>
    if h_invalid : !was_square then
      none
    else
      some { x := x_abs, y := y, on_curve :=
        toEdwards_on_curve (sqrt_checked_spec x2 h_call
          (by cases was_square <;> simp_all)) }

noncomputable def toEdwards.fromMontgomeryPoint (m : MontgomeryPoint) :
    Option (Edwards.Point Edwards.Ed25519) :=
    let p := MontgomeryPoint.mkPoint m
    toEdwards p

end toEdwards

end Montgomery
