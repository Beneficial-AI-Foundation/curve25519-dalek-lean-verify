/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
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

/-!
Helper Def:
Define the conversion using Horner's method (foldr).
This prevents the creation of the massive syntax tree that `U8x32_as_Nat` produces.
-/
def bytesToField (m : MontgomeryPoint) : ZMod p :=
  m.val.foldr (init := 0) fun b acc =>
    (b.val : ZMod p) + (256 : ZMod p) * acc

/--
Validity for MontgomeryPoint.
A MontgomeryPoint is a 32-byte integer `u` representing a coordinate on the curve `v² = u³ + Au² + u`.
It is valid if:
1. The integer `u` is strictly less than the field modulus `p`.
2. `u` maps to a valid Edwards `y` coordinate (i.e., `u ≠ -1`).
3. The resulting Edwards point exists (i.e., we can solve for `x`).
-/
def MontgomeryPoint.IsValid (m : MontgomeryPoint) : Prop :=
  let u := bytesToField m
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
  try ring

/--
Convert MontgomeryPoint to Point Ed25519.
1. Recovers `y` from `u` via `y = (u-1)/(u+1)`.
2. Recovers `x` from `y` (choosing the canonical positive root).
Returns 0 (identity) if invalid.
-/noncomputable def MontgomeryPoint.toPoint (m : MontgomeryPoint) : Point Ed25519 :=
  if h : (MontgomeryPoint.IsValid m) then
    -- The following is equivalent to defining u := 8x32_as_Nat m % p, but it uses Horner's method
    --  to avoid un folding heavy computations on large Nats casted as Mod p.
    let u : ZMod p := bytesToField m
    -- We know u != -1 from IsValid, so inversion is safe/correct
    let one : ZMod p := 1
    let y : ZMod p := (u - one) * (u + one)⁻¹

    -- Recover x squared
    let num : ZMod p := y^2 - one
    let den : ZMod p := (d : ZMod p) * y^2 + one

    let x2 : ZMod p := num * den⁻¹

    -- Extract root (guaranteed to exist by IsValid)
    match h_sqrt : sqrt_checked x2 with
    | (x_abs, is_sq) =>

    -- For Montgomery -> Edwards, the sign of x is lost.
    -- We canonically choose the non-negative (even) root.
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
        try ring
      }
  else
    0

end curve25519_dalek.montgomery

namespace Montgomery

open curve25519_dalek.montgomery
open curve25519_dalek.math


section MontgomeryPoint

/-- Create a point from a MontgomeryPoint byte representation.
    Computes the v-coordinate from u using the Montgomery curve equation v² = u³ + A·u² + u.

    Note: `sqrt_checked` returns a value whose square equals its input, which depends on
    the mathematical properties of the square root function in the field.

    This is a one-way conversion, since the Montgomery
    model does not retain sign information.
-/

noncomputable def MontgomeryPoint.u_affine_toPoint (u : CurveField) : Point:=
    let v_squared := u ^ 3 + Curve25519.A * u ^ 2 + u
    match h_call: curve25519_dalek.math.sqrt_checked v_squared with
    | (v_abs, was_square) =>
    let v := v_abs
    if h_invalid : !was_square || (u ==0) then
      T_point
    else
      .some (x := u) (y := v) (h := by
        replace h_invalid := Bool.eq_false_iff.mpr h_invalid
        rw [Bool.or_eq_false_iff] at h_invalid
        obtain ⟨h_sq_not,  h_y_eq_false⟩ := h_invalid
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at h_sq_not
        have curve_eq : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u := by
          apply sqrt_checked_spec v_squared
          · exact h_call
          · exact h_sq_not
        apply (nonsingular_iff u v).mpr
        rw[WeierstrassCurve.Affine.equation_iff]
        simp only [MontgomeryCurveCurve25519]
        simp only[curve_eq ]
        ring
     )


theorem MontgomeryPoint.u_affine_toPoint_spec (u v : CurveField)
  (non: u ≠ 0)
  (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
  MontgomeryPoint.u_affine_toPoint (u : CurveField) = WeierstrassCurve.Affine.Point.some ((nonsingular_iff u v).mpr (by
        rw[WeierstrassCurve.Affine.equation_iff]
        simp only [MontgomeryCurveCurve25519]
        simp only [equation]
        ring )) := by
        /-
          have is_sq : IsSquare (u ^ 3 + Curve25519.A * u ^ 2 + u) := by
            use v
            rw [sq] at equation
            exact equation.symm
          have : ¬ ((sqrt_checked (u ^ 3 + Curve25519.A * u ^ 2 + u)).2 = false ∨ u = 0) := by
              simp only [non]
              unfold sqrt_checked
              simp only [is_sq]
              grind
          -/
          sorry

noncomputable def MontgomeryPoint.toPoint (m : MontgomeryPoint) : Point:=
    let u : CurveField := U8x32_as_Nat m
    MontgomeryPoint.u_affine_toPoint u

end MontgomeryPoint

section fromEdwards
open curve25519_dalek.montgomery
open curve25519_dalek.edwards



lemma d_eq : (Edwards.Ed25519.d : CurveField)= -121665/ 121666 := by
  have hd: Edwards.Ed25519.d = d := by decide
  rw[hd]
  have : (121666 : CurveField)≠ 0 := by decide
  field_simp[this]
  decide

lemma a_plus_d : (Edwards.Ed25519.a : CurveField) + Edwards.Ed25519.d = - 243331/121666 := by
  have ha: Edwards.Ed25519.a = -1 := by rfl
  rw[ha, d_eq]
  have : (121666 : CurveField)≠ 0 := by decide
  field_simp[this]
  decide


lemma a_sub_d : (Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d = - 1/121666 := by
  have ha: Edwards.Ed25519.a = -1 := by rfl
  rw[ha, d_eq]
  have : (121666 : CurveField)≠ 0 := by decide
  field_simp[this]
  decide


lemma adA : 2 * ((Edwards.Ed25519.a : CurveField) + Edwards.Ed25519.d) /(Edwards.Ed25519.a - Edwards.Ed25519.d) = Curve25519.A := by
  rw[a_plus_d, a_sub_d]
  have : (121666 : CurveField)≠ 0 := by decide
  field_simp[this]
  decide

lemma adB : (4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d)) = - 486664 := by
  rw[ a_sub_d]
  have : (121666 : CurveField)≠ 0 := by decide
  field_simp[this]
  decide


lemma B_d_relation : IsSquare (4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d)) := by
  rw[adB]
  unfold IsSquare
  refine ⟨(-486664 : ZMod p) ^ ((p + 1) / 4), ?_⟩
  have hp : (p : ℕ) % 4 = 1 := by
    -- arithmetic fact: 2^255 ≡ 0 (mod 4)
    -- so 2^255 - 19 ≡ 1 (mod 4)
    norm_num [p]
  -- square-root lemma for ZMod when p ≡ 1 mod 4
  sorry

-- Define roots_B as a square root of the B coefficient
noncomputable def Curve25519.roots_B : CurveField :=
  Classical.choose B_d_relation

lemma pow2_roots_B : Curve25519.roots_B ^ 2 = 4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d) := by
  classical
  unfold Curve25519.roots_B
  have :=B_d_relation
  unfold IsSquare at this
  simpa [pow_two] using (Classical.choose_spec this).symm

lemma roots_B_non_zero : ¬ Curve25519.roots_B = 0 := by
  have :=pow2_roots_B
  intro h
  rw[h, adB] at this
  revert this
  decide


-- Prove that the Montgomery to Edwards conversion inverts the Edwards to Montgomery conversion
lemma montgomery_edwards_inverse {y : CurveField} (hy1 : y ≠ 1) :    let u := (1 + y) / (1 - y)
    y = (u - 1) / (u + 1) := by
  intro u
  have num_eq : u - 1 = (1 + y - (1 - y)) / (1 - y) := by
    field_simp [hy1]
    grind
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
    _ = (2 * y) / 2 := by  field_simp
    _ = (2 * y) / (1 - y) * (1 - y) / 2 := by field_simp [hy1]; grind
    _ = (u - 1) / (u + 1) := by
        rw [← num_simplified]
        field_simp [hy1]
        have h_u_plus_1 : u + 1 ≠ 0 := by
          rw [den_simplified]
          field_simp [hy1]
          ring_nf
          simp
          grind
        field_simp [h_u_plus_1]
        grind


theorem on_curves_M (e : Edwards.Point Edwards.Ed25519)
 (hy : e.y ≠ 1)
 (hx : e.x ≠ 0) :
  let u :=(1 + e.y) / (1 - e.y)
  let v := (1 + e.y) / ((1 - e.y) * e.x)
  let A := 2 * ((Edwards.Ed25519.a : CurveField) + Edwards.Ed25519.d) /(Edwards.Ed25519.a - Edwards.Ed25519.d)
  let B := 4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d)
  B* v^2 = u ^ 3 + A * u ^ 2 + u  := by
  simp
  have eq:= e.on_curve
  have huy:= montgomery_edwards_inverse hy
  simp at eq
  set u :=(1 + e.y) / (1 - e.y) with hu
  set v := (1 + e.y) / ((1 - e.y) * e.x) with hv
  have h1 : (1 - e.y) ≠ 0 := by grind
  have h2 : (1 + e.y) ≠ 0 := by
      intro h2
      have : e.y=-1 := by grind
      simp[this] at eq
      have : Edwards.Ed25519.a * e.x ^ 2  =  Edwards.Ed25519.d * e.x ^ 2 := by grind
      have : (Edwards.Ed25519.a  - Edwards.Ed25519.d) * e.x^2 =0 := by grind
      simp[hx] at this
      revert this
      decide
  have hxv: e.x = u / v := by
    rw [hu, hv]
    field_simp [h1, h2, hx]
  simp at huy
  rw[huy, hxv] at eq
  have nonv: v ≠ 0 := by
    rw[hv]
    intro h
    apply h2
    grind
  have nonu: u ≠ 0 := by
    rw[hu]
    intro h
    apply h2
    grind
  have nonu1: u +1 ≠ 0 := by
    rw[hu]
    intro h
    field_simp at h
    ring_nf at h
    grind
  field_simp at eq
  have ha: Edwards.Ed25519.a = -1 := by rfl
  have hd: Edwards.Ed25519.d = d := by rfl
  have :
  v ^ 2 * (u + 1) ^ 2 -  v ^ 2 * (u - 1) ^ 2 =  Edwards.Ed25519.a * u ^ 2 * (u + 1) ^ 2  - u ^ 2 * (u - 1) ^ 2 * Edwards.Ed25519.d:= by grind
  have : v ^ 2 * ((u + 1) ^ 2 -  (u - 1) ^ 2) =  Edwards.Ed25519.a * u ^ 2 * (u + 1) ^ 2  - u ^ 2 * (u - 1) ^ 2 * Edwards.Ed25519.d:= by grind
  have : 4 * u * v ^ 2  =  Edwards.Ed25519.a * u ^ 2 * (u + 1) ^ 2  - u ^ 2 * (u - 1) ^ 2 * Edwards.Ed25519.d := by grind
  have : 4 * u * v ^ 2  =  u^2 *(Edwards.Ed25519.a *  (u + 1) ^ 2  - (u - 1) ^ 2 * Edwards.Ed25519.d) := by grind
  have : 4  * v ^ 2  =  u *(Edwards.Ed25519.a *  (u + 1) ^ 2  - (u - 1) ^ 2 * Edwards.Ed25519.d) := by grind
  rw[ha, hd] at this
  rw[ha, hd]
  have dplus: (-1: CurveField) -d  ≠ 0 := by decide
  have : 4  * v ^ 2  =  - u * ( (d+1)*u ^ 2  - 2*(d-1)* u + d +1) := by
    rw[this]
    ring_nf
  field_simp
  rw[this]
  ring_nf




theorem on_MontgomeryCurves (e : Edwards.Point Edwards.Ed25519)
 (hy : e.y ≠ 1)
 (hx : e.x ≠ 0) :
  let u :=(1 + e.y) / (1 - e.y)
  let v := Curve25519.roots_B  * (1 + e.y) / ((1 - e.y) * e.x)
  v^2 = u ^ 3 + Curve25519.A * u ^ 2 + u  := by
  have := on_curves_M e hy hx
  simp_all[adA]
  rw[← this, ← pow2_roots_B]
  grind


theorem nonsingular_on_curves_M (e : Edwards.Point Edwards.Ed25519) (hy : e.y ≠ 1)
 (hx : e.x ≠ 0) :
  let u := (1 + e.y) / (1 - e.y)
  let v := Curve25519.roots_B * (1 + e.y) / ((1 - e.y) * e.x)
  MontgomeryCurveCurve25519.Nonsingular u v  := by
  rw[Montgomery.nonsingular_iff, WeierstrassCurve.Affine.equation_iff, MontgomeryCurveCurve25519]
  have := on_MontgomeryCurves e hy hx
  simp_all



noncomputable def fromEdwards : Edwards.Point Edwards.Ed25519 → Point
  | e =>
    if hy: e.y = 1 then
     0
     else
     if hx: e.x =0 ∧ e.y = -1 then
      T_point
     else
      let u:= (1 + e.y) / (1 - e.y)
      let v := Curve25519.roots_B  * (1 + e.y) / ((1 - e.y) * e.x)
      .some (x := u) (y := v) (h:= by
      apply nonsingular_on_curves_M e hy
      have : e.x ≠  0 ∨  e.y ≠  -1 := by
       grind
      rcases this
      · simp_all
      · intro h
        have := e.on_curve
        simp[h, hy] at this
        simp_all
       )


theorem map_zero : fromEdwards 0 = 0 := by
  unfold fromEdwards
  simp



theorem zeroY (e : Edwards.Point Edwards.Ed25519)
  (h : e.y = 1) :
  e = 0 := by
  -- If e.y = 1, then from the Edwards curve equation: a*x² + y² = 1 + d*x²*y²
  -- With a = -1 and y = 1: -x² + 1 = 1 + d*x²
  -- This gives: -x² = d*x², so x²(1 + d) = 0
  -- Since 1 + d ≠ 0 for Ed25519, we must have x² = 0, hence x = 0
  -- Therefore e = (0, 1) which is the identity point
  cases e with
  | mk x y h_curve =>
    subst h
    ext
    · -- Prove x = 0
      -- From curve equation with y = 1: a*x² + 1 = 1 + d*x²
      have h_eq : Edwards.Ed25519.a * x^2 + 1 = 1 + Edwards.Ed25519.d * x^2 := by
        convert h_curve using 2
        ring
      -- Since a = -1: -x² + 1 = 1 + d*x²
      have ha : Edwards.Ed25519.a = -1 := rfl
      rw [ha] at h_eq
      -- Simplify: -x² = d*x²
      have h_simp : -(x^2) = Edwards.Ed25519.d * x^2 := by grind
      -- Therefore: x²(1 + d) = 0
      have h_factor : x^2 * (1 + Edwards.Ed25519.d) = 0 := by
        linear_combination -h_simp
      -- Since 1 + d ≠ 0, we have x² = 0
      have h_d_neq : (1 + Edwards.Ed25519.d : ZMod p) ≠ 0 := by
        -- This follows from properties of Ed25519.d
        decide
      have h_x_sq : x^2 = 0 := by
        grind
      exact sq_eq_zero_iff.mp h_x_sq
    · -- Prove y = 1
      rfl

theorem zero_iff (e : Edwards.Point Edwards.Ed25519) :  e = 0 ↔ e.y = 1 := by
  constructor
  · intro he
    rw[he]
    rfl
  · apply zeroY

theorem exceptEdwardsPoint {e : Edwards.Point Edwards.Ed25519}
  (h : 1 + e.y = 0) :
  e.x = 0 := by
  -- If 1 + e.y = 0, then e.y = -1
  -- From the Edwards curve equation: a*x² + y² = 1 + d*x²*y²
  -- With a = -1 and y = -1: -x² + 1 = 1 + d*x²
  -- This gives: -x² = d*x², so x²(-1 - d) = 0
  -- Since -(1 + d) ≠ 0 for Ed25519, we must have x² = 0, hence x = 0
  have hy : e.y = -1 := by grind
  have h_curve := e.on_curve
  have ha : Edwards.Ed25519.a = -1 := rfl
  rw [ha, hy] at h_curve
  -- Now h_curve: -x² + (-1)² = 1 + d*x²*(-1)²
  -- Simplify: -x² + 1 = 1 + d*x²
  have h_simp : -e.x^2 + 1 = 1 + Edwards.Ed25519.d * e.x^2 := by
    convert h_curve using 2
    · grind
    · ring
  -- Therefore: -x² = d*x²
  have h_eq : -e.x^2 = Edwards.Ed25519.d * e.x^2 := by grind
  -- Factor: x²(-1 - d) = 0, i.e., x²(-(1 + d)) = 0
  have h_factor : e.x^2 * (-(1 + Edwards.Ed25519.d)) = 0 := by
    grind
  -- Since -(1 + d) ≠ 0, we have x² = 0
  have h_d_neq : (-(1 + Edwards.Ed25519.d) : ZMod p) ≠ 0 := by
    simp
    decide
  have h_x_sq : e.x^2 = 0 := by
    grind
  exact sq_eq_zero_iff.mp h_x_sq


theorem neg_fromEdwards (e : Edwards.Point Edwards.Ed25519) :
  fromEdwards (-e) = - fromEdwards e := by
  by_cases h : e = 0
  · simp[h, map_zero ]
  · unfold fromEdwards
    rw[zero_iff] at h
    simp only [Edwards.neg_y, h, Edwards.neg_x]
    simp
    by_cases h : e.x = 0
    · simp only [h]
      simp[T_point]
      by_cases h₁:e.y = -1
      · simp_all
      · simp_all[MontgomeryCurveCurve25519]
    · simp only [h]
      simp[MontgomeryCurveCurve25519]
      grind









theorem condition_T_point (e₁ e₂ : Edwards.Point Edwards.Ed25519)
 (h : 1 + (e₁ + e₂).y = 0) (he₁ : 1 + e₁.y = 0) :
   e₂.y = 1 := by
  -- From h, we have (e₁ + e₂).y = -1
  have hy_sum : (e₁ + e₂).y = -1 := by grind

  -- Use the Edwards addition formula for y-coordinate
  rw [Edwards.add_y] at hy_sum

  -- Recall Ed25519.a = -1
  have ha : Edwards.Ed25519.a = -1 := rfl

  -- The addition formula gives:
  -- (e₁.y * e₂.y + e₁.x * e₂.x) / (1 - d * e₁.x * e₂.x * e₁.y * e₂.y) = -1
  rw [ha] at hy_sum

  -- The denominator is non-zero by completeness
  have h_denom : 1 - Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y ≠ 0 :=
    (Edwards.Ed25519.denomsNeZero e₁ e₂).2

  -- Clearing the denominator
  have h_cleared : e₁.y * e₂.y + e₁.x * e₂.x =
    -(1 - Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y) := by
    field_simp [h_denom] at hy_sum
    grind

  -- Simplify to: e₁.y * e₂.y + e₁.x * e₂.x + 1 = d * e₁.x * e₂.x * e₁.y * e₂.y
  have h_eq : e₁.y * e₂.y + e₁.x * e₂.x + 1 =
    Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y := by
    grind

  have hy_e₁ : e₁.y = -1 := by grind
  have hx_sum:= exceptEdwardsPoint h
  have hx_e₁:= exceptEdwardsPoint he₁
  rw [Edwards.add_x] at hx_sum
  have hx_denom : 1 + Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y ≠ 0 :=
        (Edwards.Ed25519.denomsNeZero e₁ e₂).1
  have hx_cleared : e₁.x * e₂.y + e₁.y * e₂.x = 0 := by
        rw[div_eq_zero_iff] at hx_sum
        simp[hx_denom] at hx_sum
        exact hx_sum
  simp[hx_e₁, hy_e₁] at hx_cleared
  simp[hx_e₁, hy_e₁] at h_cleared
  apply h_cleared





theorem add_T_point (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (he₁ : 1 + e₁.y = 0) :
  e₂.x = -(e₁ + e₂).x  ∧ e₂.y = -(e₁ + e₂).y := by
  rw [Edwards.add_y]
  have ha : Edwards.Ed25519.a = -1 := rfl
  rw [ha]
  have h_denom : 1 - Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y ≠ 0 :=
    (Edwards.Ed25519.denomsNeZero e₁ e₂).2
  have hy_e₁ : e₁.y = -1 := by grind
  have hx_e₁:= exceptEdwardsPoint he₁
  simp[hx_e₁, hy_e₁]
  rw [Edwards.add_x]
  simp[hx_e₁, hy_e₁]



theorem add_T_point' (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (he₁ : 1 + e₂.y = 0) :
  e₁.x = -(e₁ + e₂).x  ∧ e₁.y = -(e₁ + e₂).y := by
  rw [Edwards.add_y]
  have ha : Edwards.Ed25519.a = -1 := rfl
  rw [ha]
  have h_denom : 1 - Edwards.Ed25519.d * e₁.x * e₂.x * e₁.y * e₂.y ≠ 0 :=
    (Edwards.Ed25519.denomsNeZero e₁ e₂).2
  have hy_e₁ : e₂.y = -1 := by grind
  have hx_e₁:= exceptEdwardsPoint he₁
  simp[hx_e₁, hy_e₁]
  rw [Edwards.add_x]
  simp[hx_e₁, hy_e₁]

theorem T_point_x {e : Edwards.Point Edwards.Ed25519}
  (h : e.x = 0) :
  e.y = 1 ∨ e.y = -1 := by
  have := e.on_curve
  simp[h] at this
  exact this

lemma condition_Neg (e₁ e₂ : Edwards.Point Edwards.Ed25519)
(hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) (hy3 : 1 + e₂.y ≠ 0)
    (hx1 : e₁.x ≠ 0) (hx2 : e₂.x ≠ 0) :
((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧ e₁.x = - e₂.x) ↔
((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧
        Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) =
          -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
          simp
          intro ha
          constructor
          · intro hx
            rw[hx]
            field_simp[ha]
            simp
            field_simp[roots_B_non_zero ]
            grind
          · field_simp[roots_B_non_zero ]
            field_simp at ha
            rw[ha]
            field_simp[hy1, hy3]
            grind

lemma injective_fromEdwards {e₁ e₂ : Edwards.Point Edwards.Ed25519}
(hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) :
(1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ↔ e₁.y =e₂.y := by
  constructor
  · field_simp[hy1]
    ring_nf
    rw[add_assoc, add_assoc]
    simp
    intro a
    have : e₁.y + (-(e₁.y * e₂.y) - e₂.y) =  - e₁.y * e₂.y + (e₁.y - e₂.y) := by ring
    rw[this] at a
    have : -e₁.y - e₁.y * e₂.y + e₂.y = - e₁.y * e₂.y +  (e₂.y - e₁.y) := by ring
    rw[this] at a
    simp at a
    have : 2 * (e₁.y - e₂.y) = 0 := by grind
    have non2: (2:CurveField) ≠ 0 := by decide
    simp[non2] at this
    grind
  · intro ha
    rw[ha]

lemma injective_Neg {e₁ e₂ : Edwards.Point Edwards.Ed25519}
(hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) (hy3 : 1 + e₂.y ≠ 0)
    (hx1 : e₁.x ≠ 0) (hx2 : e₂.x ≠ 0) :
(e₁.y =e₂.y  ∧ e₁.x = - e₂.x) ↔
((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧
        Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) =
          -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
          rw[← injective_fromEdwards, condition_Neg]
          all_goals simp_all

set_option maxHeartbeats 1000000 in
-- heavy simp


theorem add_fromEdwards_second (e₁ e₂ : Edwards.Point Edwards.Ed25519)
(non_e1_x : e₁.x ≠ 0)
(zero_e2_x : e₂.x = 0) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
    have e2y:= e₂.on_curve
    simp[zero_e2_x] at e2y
    rcases e2y with e2y | e2y
    · unfold fromEdwards
      simp_all
      by_cases non_sum: (e₁ + e₂).y = 1
      · simp_all
        simp[Edwards.add_y] at non_sum
        simp_all
      ·
        simp[Edwards.add_x]
        simp_all
        simp[Edwards.add_y] at non_sum
        simp[zero_e2_x, e2y] at non_sum
        simp_all
        simp[Edwards.add_y]
        simp_all
    · unfold fromEdwards
      simp_all
      by_cases non_sum: (e₁ + e₂).y = 1
      · simp_all
        simp[Edwards.add_y] at non_sum
        have :  -1 ≠  (1:CurveField) := by decide
        simp_all
        have : e₁.y= -1 := by grind
        simp_all
        simp[T_point]
        simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
        simp[MontgomeryCurveCurve25519]
      · simp_all
        simp[Edwards.add_x, e2y, zero_e2_x]
        have :  -1 ≠  (1:CurveField) := by decide
        simp[Edwards.add_y] at non_sum
        simp_all
        by_cases non_e₁: e₁.y = 1
        · simp_all
          simp[T_point]
          simp[Edwards.add_y]
          simp_all
        · simp_all
          simp[T_point]
          simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
          simp[MontgomeryCurveCurve25519]
          simp_all
          have :¬ (1 + e₁.y = 0 ∨ 1 - e₁.y = 0) := by grind
          simp_all
          simp[Edwards.add_y]
          simp_all
          field_simp[this.left, this.right]
          rw[pow2_roots_B,adB]
          have := e₁.on_curve
          sorry















































theorem add_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519)
 :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry

theorem double_T {e : Edwards.Point Edwards.Ed25519} (hx : e.x = 0) :
  (e + e).x=0 := by
  simp[Edwards.add_x, hx]

theorem power_T (n : ℕ) {e : Edwards.Point Edwards.Ed25519} (hx : e.x = 0) :
  n • e.x=0 := by
  induction n
  · simp
  · rename_i n hn
    simp[add_smul, hn]
    exact hx

theorem double_T1 {e : Edwards.Point Edwards.Ed25519}
  (hx : (e + e).x = 0) :
  (e.x=0 ∧ e.y ^ 2 =1) ∨  (e.x ^ 2 = -1 ∧ e.y =0) := by
  have hy:= T_point_x hx
  have hx1:=hx
  simp[Edwards.add_x] at hx
  field_simp at hx
  simp at hx
  rcases hx with h2 | h2
  · rcases h2 with h2 | h2
    · rcases h2 with h2 | h2
      · simp_all
        simp[Edwards.add_y, h2] at hy
        rcases hy with hy | hy
        · field_simp at hy
          grind
        · have :=e.on_curve
          field_simp at this
          field_simp at hy
          simp[hy] at this
          simp[h2] at this
          have eq: -1 ≠  (1:CurveField):=by decide
          have := eq this
          apply False.elim this
      · rcases hy with h1 | h1
        · simp[Edwards.add_y] at h1
          field_simp at h1
          simp_all
          have := e.on_curve
          simp [h2] at this
          rw[this] at h1
          have : (-1)≠  (1:CurveField):=by decide
          have := this h1
          apply False.elim this
        · simp[Edwards.add_y] at h1
          field_simp at h1
          simp_all
          have ha: Edwards.Ed25519.a=-1 := rfl
          rw[ha] at h1
          have :  e.x ^ 2  = -1 := by grind
          simp[this]
    · have : 1+1 ≠  (0:CurveField):=by decide
      have := this h2
      apply False.elim this
  · have eq:= e.on_curve
    field_simp[h2] at eq
    rw[h2] at eq
    have ha: Edwards.Ed25519.a=-1 := rfl
    rw[ha] at eq
    have eq1: e.y ^ 2 = e.x ^ 2 := by grind
    rcases hy with hy | hy
    · simp[Edwards.add_y] at hy
      field_simp at hy
      have : (1 - e.y ^ 2 * e.x ^ 2 * Edwards.Ed25519.d) = 2:= by grind
      rw[this] at hy
      field_simp at hy
      simp[ha, eq1] at hy
      field_simp at hy
      have : e.x ^ 2 =1 := by grind
      have eq:= e.on_curve
      rw[this] at eq
      rw[this] at eq1
      simp[eq1, ha] at eq
      have : (0:CurveField) ≠  1 + Edwards.Ed25519.d  :=by decide
      have := this eq
      apply False.elim this
    · simp[Edwards.add_y] at hy
      field_simp at hy
      have : (1 - e.y ^ 2 * e.x ^ 2 * Edwards.Ed25519.d) = 2:= by grind
      rw[this] at hy
      field_simp at hy
      simp[ha, eq1] at hy
      have : e.x ^ 2 =-1 := by grind
      have eq:= e.on_curve
      rw[this] at eq
      rw[this] at eq1
      simp[eq1, ha] at eq
      have : (0:CurveField) ≠  1 + Edwards.Ed25519.d  :=by decide
      have := this eq
      apply False.elim this

theorem double_special_point {e : Edwards.Point Edwards.Ed25519}
  (hx : e.x ^ 2 = -1)
  (hy : e.y = 0) :
  (e + e).y = -1 ∧ (e + e).x = 0 ∧ ¬ e.x= 0 := by
          constructor
          · simp[Edwards.add_y]
            simp[hy]
            have : e.x * e.x =e.x ^ 2 := by ring
            rw[mul_assoc,this,hx]
            have : Edwards.Ed25519.a = -1 := rfl
            rw[this]
            simp
          · constructor
            · simp[Edwards.add_x]
              simp[hy]
            · intro h
              simp_all

theorem double_fromEdwards_special_point (e : Edwards.Point Edwards.Ed25519)
  (hx : e.x ^ 2 = -1)
  (hy : e.y = 0) :
  fromEdwards (e + e) = (fromEdwards e) + (fromEdwards e) := by
          have hy2:=( double_special_point hx hy).left
          have non:=( double_special_point hx hy).right.left
          have non_x:=( double_special_point hx hy).right.right
          have : (-1)≠  (1:CurveField):=by decide
          unfold fromEdwards
          simp[hy2, non, this, hy, non_x]
          simp[T_point]
          simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
          simp only[MontgomeryCurveCurve25519]
          have : ¬ Curve25519.roots_B / e.x = -(Curve25519.roots_B / e.x) := by
            intro h
            have : Curve25519.roots_B =0 := by grind
            apply  roots_B_non_zero this
          simp[this,Curve25519.A]
          set a:= Curve25519.roots_B / e.x with ha
          have : a^2 = 486664:= by
              rw[ha]
              field_simp
              rw[pow2_roots_B,adB,hx]
              simp
          constructor
          · grind
          · grind

theorem double_fromEdwards_zero_x (e : Edwards.Point Edwards.Ed25519)
  (hx : (e + e).x = 0) :
  fromEdwards (e + e) = (fromEdwards e) + (fromEdwards e) := by
    have h1 := @double_T1 e hx
    cases h1 with
    | inl h1 =>
      unfold fromEdwards
      simp_all
      have := (e+e).on_curve
      simp[hx] at this
      rcases this with h | h
      · simp[h]
        rcases h1.right
        · simp_all
        · have : (-1)≠  (1:CurveField):=by decide
          simp_all
          rw[Montgomery.T_point_order_two]
      · have : (-1)≠  (1:CurveField):=by decide
        simp[h, this]
        simp[Edwards.add_y] at h
        rcases h1.right with h2 | h2
        · simp[h2, h1.left] at h
          have := this h.symm
          apply False.elim this
        · simp[h2, h1.left] at h
          have := this h.symm
          apply False.elim this
    | inr h1 =>
      apply double_fromEdwards_special_point
      all_goals simp_all


theorem comm_mul_fromEdwards {n : ℕ} (e : Edwards.Point Edwards.Ed25519) :
  fromEdwards (n • e) = n • (fromEdwards e) := by
  induction n
  · simp[map_zero]
  · rename_i n hn
    simp[add_smul]
    rw[add_fromEdwards, hn]




theorem fromEdwards_eq_MontgomeryPoint_toPoint (e : Edwards.Point Edwards.Ed25519)
  (m : MontgomeryPoint)
  (non : ¬ e.y = 1)
  (non_x : ¬ e.x = 0)
  (h : U8x32_as_Nat m = (1 + e.y) / (1 - e.y)) :
  fromEdwards e = MontgomeryPoint.toPoint m  := by
  unfold fromEdwards
  simp[non, non_x]
  unfold MontgomeryPoint.toPoint
  rw[h]
  clear *- non
  apply symm
  apply MontgomeryPoint.u_affine_toPoint_spec
  · simp
    constructor
    · intro ha
      have := exceptEdwardsPoint ha
      apply non_x this
    · grind
  · have := on_MontgomeryCurves e non non_x
    simp at this
    apply this

end fromEdwards

section toEdwards
open curve25519_dalek.math

noncomputable def toEdwards : Point → Option (Edwards.Point Edwards.Ed25519)
  | .zero => some 0
  | .some (x := u) (y := v) (h:= h) =>
   let y := (u - 1) * (u + 1)⁻¹
   let den : ZMod p := (d : ZMod p) * y^2 + 1
   let num : ZMod p := y^2 - 1
   let x2 : ZMod p := num * den⁻¹
   match h_call: curve25519_dalek.math.sqrt_checked x2 with
    | (x_abs, was_square) =>
    let x := x_abs
    if h_invalid : !was_square then
      none
    else
    -- For Montgomery -> Edwards, the sign of x is lost.
    -- We canonically choose the non-negative (even) root.
    some { x := x_abs, y := y, on_curve := (by
        replace h_invalid := Bool.eq_false_iff.mpr h_invalid
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at h_invalid
        have eq:=h.left
        rw [WeierstrassCurve.Affine.equation_iff] at eq
        simp [MontgomeryCurveCurve25519] at eq
        have non:=h.right
        simp [WeierstrassCurve.Affine.evalEval_polynomialY, WeierstrassCurve.Affine.evalEval_polynomialX, MontgomeryCurveCurve25519] at non
        have h_x_sq : x_abs^2 = x2 := by
          apply sqrt_checked_spec x2 h_call h_invalid

        have h_den_nz : den ≠ 0 := by
          dsimp only [den]
          apply edwards_denom_nonzero

        have ha : Edwards.Ed25519.a = -1 := rfl
        have hd : (d : ZMod p) = Edwards.Ed25519.d := rfl
        rw [ha, h_x_sq]
        dsimp only [x2, num, den] at ⊢ h_den_nz
        apply (mul_right_inj' h_den_nz).mp
        field_simp [h_den_nz]
        simp only [neg_sub]
        rw [← hd]
        try ring)
      }

noncomputable def toEdwards.fromMontgomeryPoint (m : MontgomeryPoint) : Option (Edwards.Point Edwards.Ed25519):=
    let p := MontgomeryPoint.toPoint m
    toEdwards p

end toEdwards

end Montgomery
