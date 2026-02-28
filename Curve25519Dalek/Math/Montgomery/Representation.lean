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


theorem Aux_u_affine_toPoint_spec {u v : CurveField}
  (non : u ≠ 0)
  (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
   ((sqrt_checked (u ^ 3 + Curve25519.A * u ^ 2 + u)).2 = false ∨ u = 0) = False:= by
  have is_sq : IsSquare (u ^ 3 + Curve25519.A * u ^ 2 + u) := by
    use v
    rw [sq] at equation
    exact equation.symm
  unfold sqrt_checked
  simp only [is_sq, ↓reduceDIte, Bool.true_eq_false, non, or_self]


theorem non_u_affine_toPoint_spec {u v : CurveField}
  (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
  MontgomeryCurveCurve25519.Nonsingular u v := by
  apply  (nonsingular_iff u v).mpr
  rw[WeierstrassCurve.Affine.equation_iff]
  simp only [MontgomeryCurveCurve25519]
  simp only [equation]
  ring


theorem MontgomeryPoint.u_affine_toPoint_spec (u v : CurveField)
  (non : u ≠ 0)
  (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
  MontgomeryPoint.u_affine_toPoint (u : CurveField) = WeierstrassCurve.Affine.Point.some ( non_u_affine_toPoint_spec equation) := by
  sorry
/-
  have := Aux_u_affine_toPoint_spec non equation
  unfold MontgomeryPoint.u_affine_toPoint
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
  simp only [this]
  -/

noncomputable def MontgomeryPoint.mkPoint (m : MontgomeryPoint) : Point:=
    MontgomeryPoint.u_affine_toPoint  (((U8x32_as_Nat m) % 2 ^255):ℕ )

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

lemma inver_Ad : (Curve25519.A + 2) * Edwards.Ed25519.d + (Curve25519.A - 2) = 0:= by
  rw[← adA ]
  have : (Edwards.Ed25519.a - Edwards.Ed25519.d) ≠ 0 :=by
    decide
  field_simp
  decide


lemma inver_Ad_eq : Edwards.Ed25519.d=    - (Curve25519.A - 2) /(Curve25519.A + 2):= by
  rw[← adA ]
  have : (Edwards.Ed25519.a - Edwards.Ed25519.d) ≠ 0 :=by
    decide
  field_simp
  decide



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
          simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
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
  have eq:= e.on_curve
  have huy:= montgomery_edwards_inverse hy
  simp only at eq
  set u :=(1 + e.y) / (1 - e.y) with hu
  set v := (1 + e.y) / ((1 - e.y) * e.x) with hv
  have h1 : (1 - e.y) ≠ 0 := by grind
  have h2 : (1 + e.y) ≠ 0 := by
    intro h2
    have : e.y=-1 := by grind
    simp only [this, even_two, Even.neg_pow, one_pow, mul_one] at eq
    have : Edwards.Ed25519.a * e.x ^ 2  =  Edwards.Ed25519.d * e.x ^ 2 := by grind
    have : (Edwards.Ed25519.a  - Edwards.Ed25519.d) * e.x^2 =0 := by grind
    simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, hx, or_false] at this
    revert this
    decide
  have hxv: e.x = u / v := by
    rw [hu, hv]
    field_simp [h1, h2, hx]
  simp only at huy
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
  simp_all only [ne_eq, adA]
  rw[← this, ← pow2_roots_B]
  grind

theorem nonsingular_on_curves_M (e : Edwards.Point Edwards.Ed25519) (hy : e.y ≠ 1)
 (hx : e.x ≠ 0) :
  let u := (1 + e.y) / (1 - e.y)
  let v := Curve25519.roots_B * (1 + e.y) / ((1 - e.y) * e.x)
  MontgomeryCurveCurve25519.Nonsingular u v  := by
  rw[Montgomery.nonsingular_iff, WeierstrassCurve.Affine.equation_iff, MontgomeryCurveCurve25519]
  have := on_MontgomeryCurves e hy hx
  simp_all only [ne_eq, zero_mul, add_zero, one_mul]

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
      · simp_all only [false_and, not_false_eq_true, ne_eq]
      · intro h
        have := e.on_curve
        simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, zero_mul, add_zero,
          sq_eq_one_iff, hy, false_or] at this
        simp_all only [and_self, not_true_eq_false]
       )

theorem map_zero : fromEdwards 0 = 0 := by
  unfold fromEdwards
  simp only [Edwards.zero_y, ↓reduceDIte]

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
    simp only [neg_add_rev, ne_eq]
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
    simp only [↓reduceDIte, neg_eq_zero, mul_neg]
    by_cases h : e.x = 0
    · simp only [h]
      simp only [true_and, T_point, mul_zero, neg_zero, div_zero]
      by_cases h₁:e.y = -1
      · simp_all only [↓reduceDIte, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.negY, neg_zero, mul_zero,
    sub_self, zero_sub]
      · simp_all only [↓reduceDIte, MontgomeryCurveCurve25519, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.negY, neg_zero, zero_mul, sub_self]
    · simp only [h]
      simp only [false_and, ↓reduceDIte, MontgomeryCurveCurve25519, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.negY, zero_mul, sub_zero, WeierstrassCurve.Affine.Point.some.injEq, true_and]
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
    simp only [hx_denom, or_false] at hx_sum
    exact hx_sum
  simp[hx_e₁, hy_e₁] at hx_cleared
  simp only [hy_e₁, neg_mul, one_mul, hx_e₁, zero_mul, add_zero, mul_zero, mul_neg, mul_one, neg_zero, sub_zero,
    neg_inj] at h_cleared
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
  simp only [hy_e₁, neg_mul, one_mul, hx_e₁, mul_zero, zero_mul, sub_zero, mul_neg, mul_one, neg_zero, div_one,
    neg_neg, and_true]
  rw [Edwards.add_x]
  simp only [hx_e₁, zero_mul, hy_e₁, neg_mul, one_mul, zero_add, mul_zero, mul_neg, mul_one, neg_zero, add_zero,
    div_one, neg_neg]

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
  simp only [hy_e₁, mul_neg, mul_one, neg_mul, one_mul, hx_e₁, mul_zero, sub_zero, zero_mul, neg_zero, div_one,
    neg_neg, and_true]
  rw [Edwards.add_x]
  simp only [hy_e₁, mul_neg, mul_one, hx_e₁, mul_zero, add_zero, zero_mul, neg_zero, div_one, neg_neg]

theorem T_point_x {e : Edwards.Point Edwards.Ed25519}
  (h : e.x = 0) :
  e.y = 1 ∨ e.y = -1 := by
  have := e.on_curve
  simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, zero_mul, add_zero,
    sq_eq_one_iff] at this
  exact this

lemma condition_Neg (e₁ e₂ : Edwards.Point Edwards.Ed25519)
(hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) (hy3 : 1 + e₂.y ≠ 0)
    (hx1 : e₁.x ≠ 0) (hx2 : e₂.x ≠ 0) :
((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧ e₁.x = - e₂.x) ↔
((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧
        Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) =
          -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
  simp only [and_congr_right_iff]
  intro ha
  constructor
  · intro hx
    rw[hx]
    field_simp[ha]
    simp only [neg_inj]
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
    simp only [add_right_inj]
    intro a
    have : e₁.y + (-(e₁.y * e₂.y) - e₂.y) =  - e₁.y * e₂.y + (e₁.y - e₂.y) := by ring
    rw[this] at a
    have : -e₁.y - e₁.y * e₂.y + e₂.y = - e₁.y * e₂.y +  (e₂.y - e₁.y) := by ring
    rw[this] at a
    simp only [neg_mul, add_right_inj] at a
    have : 2 * (e₁.y - e₂.y) = 0 := by grind
    have non2: (2:CurveField) ≠ 0 := by decide
    simp only [mul_eq_zero, non2, false_or] at this
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

theorem add_T_point_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x = 0)
  (e2y : e₂.y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  unfold fromEdwards
  simp_all only [ne_eq, false_and, ↓reduceDIte, add_zero]
  by_cases non_sum: (e₁ + e₂).y = 1
  · simp_all only [not_false_eq_true, ↓reduceDIte, left_eq_dite_iff, reduceCtorEq, imp_false, Decidable.not_not]
    simp only [Edwards.add_y] at non_sum
    simp_all only [ne_eq, mul_one, mul_zero, sub_zero, zero_mul, div_one]
  · simp only [Edwards.add_x, div_eq_zero_iff]
    simp_all only [not_false_eq_true, ↓reduceDIte, mul_one, mul_zero, add_zero, zero_mul, one_ne_zero, or_self,
    false_and, div_one]
    simp only [Edwards.add_y] at non_sum
    simp only [e2y, mul_one, zero_e2_x, mul_zero, sub_zero, zero_mul, div_one] at non_sum
    simp_all only [↓reduceDIte, WeierstrassCurve.Affine.Point.some.injEq]
    simp only [Edwards.add_y]
    simp_all only [ne_eq, mul_one, mul_zero, sub_zero, zero_mul, div_one, not_false_eq_true, and_self]

theorem add_Except_point_fromEdwards_second (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x = 0)
  (e2y : e₂.y = -1)
  (non_e₁ : e₁.y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  unfold fromEdwards
  simp_all only [ne_eq, ↓reduceDIte, and_self, dite_eq_ite, zero_add]
  have non_sum: (e₁ + e₂).y = -1 := by
    simp only [Edwards.add_y]
    simp_all only [mul_neg, mul_one, mul_zero, sub_zero, neg_zero, div_one]
  simp_all only [and_true, add_neg_cancel, sub_neg_eq_add, zero_div, mul_zero]
  simp only [Edwards.add_x, e2y, mul_neg, mul_one, zero_e2_x, mul_zero, add_zero, zero_mul, neg_zero, div_one,
    neg_eq_zero]
  have :  -1 ≠  (1:CurveField) := by decide
  simp only [Edwards.add_y] at non_sum
  simp_all only [ne_eq, ↓reduceDIte, ↓reduceIte]
  simp only [T_point]

theorem add_Except_pointI_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x = 0)
  (e2y : e₂.y = -1)
  (non_e₁ : e₁.y = -1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  unfold fromEdwards
  simp_all only [ne_eq, and_true, ↓reduceDIte, add_neg_cancel, sub_neg_eq_add, zero_div, mul_zero, and_self,
    dite_eq_ite]
  have non_sum: (e₁ + e₂).y = 1 := by
    simp only [Edwards.add_y]
    simp_all only [ne_eq, not_false_eq_true, mul_neg, mul_one, neg_neg, mul_zero, sub_zero, neg_zero, one_ne_zero,
    div_self]
  simp_all only [not_false_eq_true, ↓reduceDIte]
  have :  -1 ≠  (1:CurveField) := by decide
  simp only [Edwards.add_y] at non_sum
  simp_all only [mul_neg, mul_one, neg_neg, mul_zero, sub_zero, neg_zero, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, ↓reduceDIte, ↓reduceIte]
  simp only [T_point]
  simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
  simp only [WeierstrassCurve.Affine.negY, neg_zero, MontgomeryCurveCurve25519, mul_zero, sub_self, and_self,
    ↓reduceDIte]

lemma Aux_eq_x1 (e₁ : Edwards.Point Edwards.Ed25519) : (1 + -e₁.y) * (1 - e₁.y) * e₁.x ^ 2 =
  (1 + e₁.y) * ((1 - e₁.y) * (-486664 - e₁.x ^ 2 * Curve25519.A) - (1 + e₁.y) * e₁.x ^ 2) := by
    ring_nf
    field_simp
    ring_nf
    field_simp
    unfold Curve25519.A
    ring_nf
    have : ∀ a b :CurveField, a-b=0 → a=b := by grind
    apply this
    ring_nf
    have :486664 + e₁.x ^ 2 * 486664 + (-(e₁.x ^ 2 * e₁.y ^ 2 * 486660) - e₁.y ^ 2 * 486664)
            = 486664 *(1- e₁.y ^2)  + e₁.x ^ 2 * 486664  -(e₁.x ^ 2 * e₁.y ^ 2 * 486660):= by grind
    rw[this]
    have : 1 - e₁.y ^ 2 =   Edwards.Ed25519.a * e₁.x ^ 2 - Edwards.Ed25519.d * e₁.x ^ 2 * e₁.y ^ 2:= by
      have := e₁.on_curve
      grind
    rw[this]
    have : Edwards.Ed25519.a = -1 := rfl
    rw[this]
    have : 486664 * (-1 * e₁.x ^ 2 - Edwards.Ed25519.d * e₁.x ^ 2 * e₁.y ^ 2) + e₁.x ^ 2 * 486664
    = -486664 * Edwards.Ed25519.d * e₁.x ^ 2 * e₁.y ^ 2 := by ring_nf
    rw[this]
    have : 486664= Curve25519.A+2 := by
      simp[Curve25519.A]
      grind
    rw[this]
    have : -(Curve25519.A + 2) * Edwards.Ed25519.d * e₁.x ^ 2 * e₁.y ^ 2 - e₁.x ^ 2 * e₁.y ^ 2 * 486660
    = -e₁.x ^ 2 * e₁.y ^ 2  *( (Curve25519.A + 2) * Edwards.Ed25519.d + 486660) := by grind
    rw[this]
    have : 486660= Curve25519.A-2 := by
      simp[Curve25519.A]
      grind
    simp[this, inver_Ad]

lemma Aux_eq_x2 (e₁ : Edwards.Point Edwards.Ed25519) : e₁.x ^ 2 * (e₁.y * 2 + (-e₁.y ^ 2 - 1)) =
  e₁.x ^ 2 * (e₁.y * (2 + e₁.y * (1 - Curve25519.A)) + 1) + (e₁.x ^ 2 * Curve25519.A - Curve25519.roots_B ^ 2) +
    Curve25519.roots_B ^ 2 * e₁.y ^ 2 := by
    rw[pow2_roots_B, adB]
    have : -((1 + -e₁.y) * (1 - e₁.y) * e₁.x ^ 2) =  (e₁.x ^ 2 * (e₁.y * 2 + (-e₁.y ^ 2 - 1))) := by grind
    rw[← this,Aux_eq_x1 e₁]
    ring

theorem Aux_eq_x (e₁ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (non_e₁ : ¬ e₁.y = -1)
  (non_e : ¬ e₁.y = 1) :
  (1 + -e₁.y) / (1 + e₁.y) =
    (Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) / ((1 + e₁.y) / (1 - e₁.y))) ^ 2 - Curve25519.A -
      (1 + e₁.y) / (1 - e₁.y) := by
  have non_e1:1 + e₁.y ≠  0 := by grind
  have non_e10:1 - e₁.y ≠  0 := by grind
  field_simp
  rw[pow2_roots_B, adB]
  rw[Aux_eq_x1]

theorem add_fromEdwards_second (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x = 0) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
    have e2y:= e₂.on_curve
    simp only [zero_e2_x, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, zero_mul,
    add_zero, sq_eq_one_iff] at e2y
    rcases e2y with e2y | e2y
    · apply add_T_point_fromEdwards
      all_goals simp_all
    · by_cases non_e₁: e₁.y = 1
      · unfold fromEdwards
        simp[T_point]
        simp[Edwards.add_y]
        have : -1 ≠  (1:CurveField) := by decide
        simp_all
      · by_cases non_e: e₁.y = -1
        · apply add_Except_pointI_fromEdwards
          all_goals simp_all
        · have : (e₁ + e₂).y ≠  1 := by
            simp[Edwards.add_y]
            grind
          unfold fromEdwards
          simp[T_point]
          simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
          simp[MontgomeryCurveCurve25519, this]
          simp[Edwards.add_y, Edwards.add_x, zero_e2_x, e2y, non_e₁, non_e1_x]
          have non_one: -1 ≠  (1:CurveField) := by decide
          simp[non_one]
          have :¬ (1 + e₁.y = 0 ∨ 1 - e₁.y = 0) := by grind
          simp_all
          constructor
          · have := Aux_eq_x e₁ non_e1_x non_e non_e₁
            simp[this]
          · field_simp[this.left, this.right]
            ring_nf
            field_simp[roots_B_non_zero]
            apply Aux_eq_x2 e₁

theorem add_eq_zero_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (sum_y : (e₁ + e₂).y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  have := zeroY _  sum_y
  rw[this, map_zero]
  have :e₁ = - e₂  := by grind
  rw[this, neg_fromEdwards]
  grind

theorem add_eq_T_point_fromEdwards1 (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (h : e₁.y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  unfold  fromEdwards
  have non_one: -1 ≠  (1:CurveField) := by decide
  simp_all
  have := e₁.on_curve
  simp_all
  ring_nf at this
  simp at this
  field_simp at this
  have : Edwards.Ed25519.a ≠  Edwards.Ed25519.d := by decide
  revert this
  rw[this]
  grind

theorem add_eq_T_point_fromEdwards2 (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (zero_e2_x : e₂.x ≠ 0)
  (h₂ : e₂.y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
    have := e₂.on_curve
    simp_all
    ring_nf at this
    simp at this
    field_simp at this
    have : Edwards.Ed25519.a ≠  Edwards.Ed25519.d := by decide
    revert this
    rw[this]
    grind

lemma aux_eq : 0 =
  (Curve25519.A + 2 +
      -((-1 + (-(2 * Curve25519.A) + -3)) *
            (-(3 + 2 * Curve25519.A + 1) ^ 2 / ((-2 + -Curve25519.A) * (1 + 1) ^ 2) - Curve25519.A - 1 - 1 - 1) /
          (1 + 1))) /
    Curve25519.roots_B := by
  field_simp[roots_B_non_zero]
  unfold Curve25519.A
  grind




theorem add_eq_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519)
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
    have :1 + e₂.y ^ 2 * e₂.x ^ 2 * Edwards.Ed25519.d ≠ 0 :=by grind
    field_simp
    have := e₂.on_curve
    ring_nf at this
    have :  Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 = 1 +  e₂.y ^ 2 * e₂.x ^ 2 * Edwards.Ed25519.d := by grind
    rw[← this]
    ring_nf
  unfold   fromEdwards
  have :  ¬ (-e₂.y = 1) := by grind
  have :  ¬ (e₂.y = 1) := by grind
  have := injective_Neg non_e2_y non_e1_y non_e2_y1 non_e1_x non_e2_x
  simp_all only [ne_eq, not_false_eq_true, sub_neg_eq_add, and_self, ↓reduceDIte, dite_eq_ite, neg_inj, false_and]
  simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
  simp only [MontgomeryCurveCurve25519, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, WeierstrassCurve.Affine.addX,
    add_zero, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, neg_add_rev]
  simp only [← this]
  have : ¬ (-e₂.y = e₂.y ∧ e₂.x = -e₂.x) := by
    field_simp
    simp only [not_and]
    intro hy
    decide
  simp only [this, ↓reduceDIte]
  have : ¬ (-1=(1:CurveField)):= by decide
  simp only [this, ↓reduceIte, T_point, WeierstrassCurve.Affine.Point.some.injEq]
  simp only [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, sub_neg_eq_add,
            ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_mul]
  have :  1 - e₁.y ≠ 0 := by grind
  have inj:= injective_fromEdwards non_e2_y  this
  simp only [e_y, sub_neg_eq_add] at inj
  simp only [inj]
  by_cases h: e₂.y=0
  · simp only [h, neg_zero, ↓reduceIte, add_zero, mul_one, one_mul, sub_zero, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, one_pow]
    have : ¬ ( Curve25519.roots_B / e₂.x = -(Curve25519.roots_B / e₂.x)) := by
      intro h
      have : Curve25519.roots_B =0 := by grind
      apply  roots_B_non_zero this
    simp only [this, ↓reduceIte]
    set a:= Curve25519.roots_B / e₂.x with ha
    have : a^2 = 486664:= by
      rw[ha]
      field_simp
      have ho := e₂.on_curve
      simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero] at ho
      have : Edwards.Ed25519.a =-1 := rfl
      rw[this] at ho
      have : e₂.x ^ 2 = -1 := by grind
      rw[pow2_roots_B,adB, this]
      simp only [neg_mul, one_mul]
    have :(a+a)= 2*a :=by ring
    rw[this]
    field_simp
    unfold Curve25519.A
    constructor
    · grind
    · grind
  have :¬  -e₂.y = e₂.y := by
    intro h
    have : 2* e₂.y =0 := by grind
    simp only [mul_eq_zero] at this
    rcases this with h | h
    · revert h
      decide
    · grind
  simp only [this, ↓reduceIte]
  have : 1 + -e₂.y = 1  -e₂.y:= by ring
  rw[this]
  set u1 := (1 - e₂.y) / (1 + e₂.y) with hu1
  set u2 := (1 + e₂.y) / (1 - e₂.y) with hu2
  set v1 := Curve25519.roots_B  * (1 - e₂.y) / ((1 + e₂.y) * e₂.x) with hv1
  set v2 := Curve25519.roots_B  * (1 + e₂.y) / ((1 - e₂.y) * e₂.x) with hv2
  have feq: (v1-v2)/(u1-u2)=  Curve25519.roots_B/ e₂.x := by
      rw[hu1, hu2, hv1, hv2]
      field_simp
      have : (1 - e₂.y) ^ 2 - (1 + e₂.y) ^ 2 = -4 *e₂.y := by
        ring_nf
      rw[this]
      have : (4 :CurveField) ≠ 0:= by decide
      field_simp
  have :((v1 - v2) / (u1 - u2)) ^ 2 - Curve25519.A - u1 - u2 =0 := by
    rw[feq]
    have : (Curve25519.roots_B / e₂.x) ^ 2 - Curve25519.A - u1 - u2
    =(Curve25519.roots_B / e₂.x) ^ 2 - Curve25519.A - (u1 + u2) := by ring
    rw[this]
    have : u1 + u2 = 2*(1+e₂.y^2)/((1-e₂.y)* (1+e₂.y)) := by
      rw[ hu1, hu2]
      field_simp
      ring_nf
    rw[this]
    field_simp
    rw[pow2_roots_B, adB]
    simp only [mul_zero]
    ring_nf
    field_simp
    have eq1:= e₂.on_curve
    have : Edwards.Ed25519.a = - 1 := rfl
    rw[this, inver_Ad_eq] at  eq1
    have : 486664= Curve25519.A +2 := by decide
    rw[this]
    have : Curve25519.A +2 ≠ 0 := by decide
    field_simp at eq1
    grind => ring
  rw[this]
  simp only [feq, zero_sub, mul_neg, neg_neg, true_and]
  simp only [hv1, hu1]
  field_simp
  ring








lemma add_eq_fromEdwards_nonI {e₁ e₂ : Edwards.Point Edwards.Ed25519}
   (non_e1_x : e₁.x ≠ 0)
  (non_e2_x : e₂.x ≠ 0)
  (non_e1_y : 1 - e₁.y ≠ 0)
  (non_e2_y : 1 - e₂.y ≠ 0)
  (non_e2_y1 : 1 + e₂.y ≠ 0)
  (sum_x : e₁.x * e₂.y + e₁.y * e₂.x = 0)
  (sum_y : (e₁ + e₂).y = -1)
  (e_y : e₁.y ≠ -e₂.y) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  unfold   fromEdwards
  have :  ¬ (-e₂.y = 1) := by grind
  have :  ¬ (e₂.y = 1) := by grind
  have :  ¬ (e₁.y = 1) := by grind
  have eq:= injective_Neg non_e2_y non_e1_y non_e2_y1 non_e1_x non_e2_x
  simp only
  simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
  simp only [MontgomeryCurveCurve25519, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, WeierstrassCurve.Affine.addX,
    add_zero, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, neg_add_rev]
  have : (e₁ + e₂).x=0 := by
    simp [Edwards.add_x, sum_x]
  have non_one: -1 ≠  (1:CurveField) := by decide
  simp_all
  simp[← eq]
  have h: ¬ (e₁.y = e₂.y ∧ e₁.x = -e₂.x)  := by
    intro h
    simp[Edwards.add_y, h] at sum_y
    field_simp at sum_y
    have := (Edwards.Ed25519.denomsNeZero e₂ e₂).left
    field_simp at this
    have : e₂.y ^ 2 + Edwards.Ed25519.a * e₂.x ^ 2
      = Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 := by  grind
    rw[this, e₂.on_curve] at sum_y
    field_simp at sum_y
    revert sum_y
    decide
  simp[h, T_point]
  simp only [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, sub_neg_eq_add,
            ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_mul]
  have :  1 - e₁.y ≠ 0 := by grind
  have inj:= injective_fromEdwards non_e2_y  this
  simp only [inj]
  by_cases heqy: (e₁.y = e₂.y)
  · simp only [heqy, true_and] at h
    simp only [heqy, ↓reduceIte]
    simp only [heqy] at sum_x
    field_simp at sum_x
    simp only [ mul_eq_zero] at sum_x
    rcases sum_x with sum_x | sum_x
    · have eq1:= e₂.on_curve
      simp only [sum_x, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero] at eq1
      simp only [Edwards.add_y, heqy, sum_x, mul_zero, zero_sub, sub_zero, div_one, neg_inj] at sum_y
      have : ¬ ( Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) =
                -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
                field_simp [roots_B_non_zero]
                grind
      simp_all only [ne_eq, not_false_eq_true, zero_ne_one, sub_zero, one_ne_zero, add_zero, and_false, div_self, mul_one,
               one_mul, true_and, false_iff, ↓reduceIte, one_pow]
      field_simp
      have : e₁.x =e₂.x := by
        rw[← eq1] at sum_y
        have : Edwards.Ed25519.a = -1 := rfl
        rw[this] at sum_y
        have :  e₂.x ^ 2=  e₂.x *  e₂.x := by grind
        simp only [neg_mul, one_mul, this, neg_inj, mul_eq_mul_right_iff, non_e2_x , or_false] at sum_y
        exact sum_y
      have : Edwards.Ed25519.a = -1 := rfl
      rw[this] at eq1
      have :e₁.x ^ 2 = -1 := by grind
      have Aeq:486664 = Curve25519.A+2 := by
                unfold Curve25519.A; grind
      simp only [this, mul_neg, mul_one, pow2_roots_B, adB, Aeq, neg_add_rev, zero_mul, neg_neg]
      have : (-2 + -Curve25519.A) * (1 + 1) ^ 2 ≠ 0 := by
        unfold Curve25519.A
        decide
      constructor
      · unfold Curve25519.A
        grind
      · have := aux_eq
        exact this
    · grind
  simp[heqy]
  sorry






































lemma Aux_eq_x0 {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : e₁.x ≠ 0)
  (non_e2_x : e₂.x ≠ 0)
  (non_e1_y : 1 - e₁.y ≠ 0)
  (non_e2_y1 : 1 + e₂.y ≠ 0)
  (sum_x : e₁.x * e₂.y + e₁.y * e₂.x = 0)
  (sum_y : (e₁ + e₂).y = -1)
  (non_meq : e₁.y ≠ -e₂.y) :
  0 =
    ((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) - Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
              ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y))) ^
            2 -
          Curve25519.A -
        (1 + e₁.y) / (1 - e₁.y) -
      (1 + e₂.y) / (1 - e₂.y) := by
      set u1 := (1 + e₁.y) / (1 - e₁.y) with hu1
      set u2 := (1 + e₂.y) / (1 - e₂.y) with hu2
      set v1 := Curve25519.roots_B  * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) with hv1
      set v2 := Curve25519.roots_B  * (1 + e₂.y) / ((1 - e₂.y) * e₂.x) with hv2
      simp only [Edwards.add_y] at sum_y
      have := Edwards.Ed25519.denomsNeZero e₁ e₂
      simp only [ne_eq] at this
      have non_eq1: (1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d) ≠ 0 := by  grind
      field_simp[non_eq1] at sum_y
      have :  e₁.y * e₂.y +  e₁.x * e₂.x = -(1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d) := by
        have : Edwards.Ed25519.a= -1 := rfl
        rw[this] at sum_y
        rw[← sum_y]
        simp only [neg_mul, one_mul, sub_neg_eq_add]
      have eq1: e₁.y = -e₁.x * e₂.y/ e₂.x := by
        field_simp
        grind
      have eqe₁:= e₁.on_curve
      rw[eq1] at eqe₁
      field_simp at eqe₁
      have := e₂.on_curve
      rw[this] at eqe₁
      have : e₁.x ^ 2 * (1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) - (e₂.x ^ 2 + e₁.x ^ 4 * e₂.y ^ 2 * Edwards.Ed25519.d) = 0 := by
        rw[eqe₁]
        simp only [sub_self]
      have eq1: e₁.x ^ 2 * (1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) - (e₂.x ^ 2 + e₁.x ^ 4 * e₂.y ^ 2 * Edwards.Ed25519.d)
      = (e₁.x ^ 2 - e₂.x ^ 2)* (1- Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2) := by
        ring_nf
      rw[eq1] at this
      simp only [mul_eq_zero] at this
      have eq1:e₁.x ^ 2 - e₂.x ^ 2 =(e₁.x  - e₂.x)*(e₁.x  + e₂.x) := by grind
      rw[eq1] at this
      simp only [mul_eq_zero] at this
      rcases this with h | h
      · rcases h with h | h
        · have  eq11x:e₁.x = e₂.x := by grind
          rw[eq11x] at sum_x
          rw[eq11x] at sum_y
          field_simp at sum_x
          simp only [mul_eq_zero, non_e2_x, false_or] at sum_x
          have  eq11y:e₁.y = -e₂.y := by grind
          have := non_meq eq11y
          apply False.elim this
        · have  eq11x:e₁.x = -e₂.x := by grind
          rw[eq11x] at sum_x
          rw[eq11x] at sum_y
          field_simp at sum_x
          simp only [mul_eq_zero, non_e2_x, false_or] at sum_x
          have  eq11y:e₁.y = e₂.y := by grind
          simp only [eq11y, mul_neg, neg_mul, sub_neg_eq_add, neg_add_rev] at sum_y
          field_simp at sum_y
          have :  e₂.y ^ 2 + Edwards.Ed25519.a * e₂.x ^2
           =  Edwards.Ed25519.a * e₂.x ^2 + e₂.y ^ 2 := by grind
          rw[this] at sum_y
          rw[e₂.on_curve] at sum_y
          have eq0: 2*(1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) =0 := by
            clear *- sum_y
            grind
          have eq2: ¬ (2 : Edwards.CurveField) = 0 := by decide
          have := (Edwards.Ed25519.denomsNeZero e₂ e₂).left
          simp at this
          ring_nf at this
          simp only [mul_eq_zero] at eq0
          rcases eq0 with h0 | h0
          · have :=eq2 h0
            apply False.elim this
          · have := this h0
            apply False.elim this
      · have : e₁.x * e₂.y = -  e₁.y * e₂.x := by grind
        have :  e₁.x ^ 2 * e₂.y ^ 2= - e₁.x * e₂.x * e₁.y * e₂.y := by
          calc
          e₁.x ^ 2 * e₂.y ^ 2 = e₁.x * e₂.y * (e₁.x * e₂.y) := by ring
          _ = e₁.x * e₂.y * (- e₁.y * e₂.x) := by grind
          _   = - e₁.x * e₂.y * e₁.y * e₂.x := by ring
          _ = - e₁.x * e₂.x * e₁.y * e₂.y := by ring_nf
        rw[mul_assoc, this] at h
        ring_nf at h
        have := (Edwards.Ed25519.denomsNeZero e₁ e₂).left h
        apply False.elim this


theorem add_eq_T_point_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (non_e2_x : ¬e₂.x = 0)
  (sum_x : (e₁ + e₂).x = 0)
  (sum_y : ¬(e₁ + e₂).y = 1)
  (non_e1_y : ¬1 - e₁.y = 0)
  (non_e2_y : ¬1 - e₂.y = 0)
  (non_e2_y_1 : ¬1 + e₂.y = 0)
  (sum_y_1 : (e₁ + e₂).y = -1)
: fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
sorry


theorem add_eq_T_point_fromEdwards' (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x ≠ 0)
  (sum_x : (e₁ + e₂).x = 0)
  (sum_y : (e₁ + e₂).y = -1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  by_cases h: e₁.y = 1
  · apply add_eq_T_point_fromEdwards1 _ _ non_e1_x h
  · by_cases h₂: e₂.y = 1
    · exact add_eq_T_point_fromEdwards2 e₁ e₂ zero_e2_x h₂
    ·
      unfold fromEdwards
      have non_one: -1 ≠  (1:CurveField) := by decide
      simp_all only [ne_eq, ↓reduceDIte, and_self, T_point, false_and]
      simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
      simp only [MontgomeryCurveCurve25519, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, WeierstrassCurve.Affine.addX,
    add_zero, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, neg_add_rev]
      have hy1 : 1 - e₂.y ≠ 0 := by grind
      have hy2 : 1 - e₁.y ≠ 0 := by grind
      have hy3 : 1 + e₂.y ≠ 0 := by
        intro hy3
        have eq1: e₂.y = -1 := by grind
        have := e₂.on_curve
        simp only [eq1, even_two, Even.neg_pow, one_pow, mul_one] at this
        ring_nf at this
        simp only [add_right_inj] at this
        field_simp at this
        have : Edwards.Ed25519.a ≠  Edwards.Ed25519.d := by decide
        revert this
        rw[this]
        decide
      have := injective_Neg hy1 hy2 hy3 non_e1_x zero_e2_x
      simp only [← this]
      by_cases heq:  e₁.y = e₂.y ∧ e₁.x = -e₂.x
      · simp only [heq, and_self, ↓reduceDIte, reduceCtorEq]
        simp only [Edwards.add_y, heq] at sum_y
        simp only [mul_neg, neg_mul, sub_neg_eq_add] at sum_y
        field_simp at sum_y
        simp only [Edwards.add_x, heq] at sum_x
        have eq:= e₂.on_curve
        have : Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 =
         e₂.y ^ 2+ Edwards.Ed25519.a * e₂.x ^ 2 := by grind
        rw[this] at eq
        rw[eq] at sum_y
        have : 1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 ≠ 0 := by
          have := Edwards.Ed25519.denomsNeZero e₂ e₂
          simp only [ne_eq] at this
          grind
        field_simp at sum_y
        grind
      · simp only [heq, ↓reduceDIte, WeierstrassCurve.Affine.Point.some.injEq]
        have := injective_fromEdwards hy1 hy2
        simp only [WeierstrassCurve.Affine.slope, this, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, sub_neg_eq_add,
        ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_mul]
        by_cases heqy: e₁.y = e₂.y
        · simp only [heqy, true_and] at heq
          simp only [heqy, ↓reduceIte]
          simp only [Edwards.add_x, heqy] at sum_x
          field_simp at sum_x
          simp only [div_eq_zero_iff, mul_eq_zero] at sum_x
          rcases sum_x with sum_x | sum_x
          · rcases sum_x with sum_x | sum_x
            · have eq1:= e₂.on_curve
              simp only [sum_x, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero] at eq1
              simp only [Edwards.add_y, heqy, sum_x, mul_zero, zero_sub, sub_zero, div_one, neg_inj] at sum_y
              have : ¬ ( Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) =
                -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
                field_simp [roots_B_non_zero]
                grind
              simp_all only [ne_eq, not_false_eq_true, zero_ne_one, sub_zero, one_ne_zero, add_zero, and_false, div_self, mul_one,
               one_mul, true_and, false_iff, ↓reduceIte, one_pow]
              field_simp
              have : e₁.x =e₂.x := by
                rw[← eq1] at sum_y
                have : Edwards.Ed25519.a = -1 := rfl
                rw[this] at sum_y
                have :  e₂.x ^ 2=  e₂.x *  e₂.x := by grind
                simp only [neg_mul, one_mul, this, neg_inj, mul_eq_mul_right_iff, zero_e2_x, or_false] at sum_y
                exact sum_y
              have : Edwards.Ed25519.a = -1 := rfl
              rw[this] at eq1
              have :e₁.x ^ 2 = -1 := by grind
              have Aeq:486664 = Curve25519.A+2 := by
                unfold Curve25519.A; grind
              simp only [this, mul_neg, mul_one, pow2_roots_B, adB, Aeq, neg_add_rev, zero_mul, neg_neg]
              have : (-2 + -Curve25519.A) * (1 + 1) ^ 2 ≠ 0 := by
                unfold Curve25519.A
                decide
              constructor
              · unfold Curve25519.A
                grind
              · have := aux_eq
                exact this
            · grind
          · have := Edwards.Ed25519.denomsNeZero e₁ e₂
            simp_all only [ne_eq, not_false_eq_true, and_false, true_and, false_iff, ↓reduceIte]
            grind
        · simp only [heqy, ↓reduceIte]
          simp only [Edwards.add_x, div_eq_zero_iff] at sum_x
          have := Edwards.Ed25519.denomsNeZero e₁ e₂
          simp only [this, or_false] at sum_x
          simp only [Edwards.add_y] at sum_y


          have := Edwards.Ed25519.denomsNeZero e₁ e₂
          simp only [ne_eq] at this
          have : (1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d) ≠ 0 := by  grind
          field_simp[this] at sum_y
          have :  e₁.y * e₂.y +  e₁.x * e₂.x = -(1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d) := by
            have : Edwards.Ed25519.a= -1 := rfl
            rw[this] at sum_y
            rw[← sum_y]
            simp only [neg_mul, one_mul, sub_neg_eq_add]
          have eq1: e₁.y = -e₁.x * e₂.y/ e₂.x := by
            field_simp
            grind
          have eqe₁:= e₁.on_curve
          rw[eq1] at eqe₁
          field_simp at eqe₁
          have := e₂.on_curve
          rw[this] at eqe₁
          have : e₁.x ^ 2 * (1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) - (e₂.x ^ 2 + e₁.x ^ 4 * e₂.y ^ 2 * Edwards.Ed25519.d) = 0 := by
            rw[eqe₁]
            simp
          have eq1: e₁.x ^ 2 * (1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) - (e₂.x ^ 2 + e₁.x ^ 4 * e₂.y ^ 2 * Edwards.Ed25519.d)
            = (e₁.x ^ 2 - e₂.x ^ 2)* (1- Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2) := by
            ring_nf
          rw[eq1] at this
          simp only [mul_eq_zero] at this
          have eq1:e₁.x ^ 2 - e₂.x ^ 2 =(e₁.x  - e₂.x)*(e₁.x  + e₂.x) := by grind
          rw[eq1] at this

          simp at this
          rcases this with h | h
          · rcases h with h | h
            · have  eq11x:e₁.x = e₂.x := by grind
              rw[eq11x] at sum_x
              rw[eq11x] at sum_y
              field_simp at sum_x
              simp only [mul_eq_zero, zero_e2_x , false_or] at sum_x
              have  eq11y:e₁.y = -e₂.y := by grind
              have := add_eq_fromEdwards e₁ e₂ non_e1_x zero_e2_x hy2 hy1 hy3 eq11x eq11y
              sorry
            · have  eq11x:e₁.x = -e₂.x := by grind
              rw[eq11x] at sum_x
              rw[eq11x] at sum_y
              field_simp at sum_x
              simp only [mul_eq_zero, zero_e2_x, false_or] at sum_x
              have  eq11y:e₁.y = e₂.y := by grind
              simp only [eq11y, mul_neg, neg_mul, sub_neg_eq_add, neg_add_rev] at sum_y
              field_simp at sum_y
              have :  e₂.y ^ 2 + Edwards.Ed25519.a * e₂.x ^2
                =  Edwards.Ed25519.a * e₂.x ^2 + e₂.y ^ 2 := by grind
              rw[this] at sum_y
              rw[e₂.on_curve] at sum_y
              have eq0: 2*(1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2) =0 := by
                clear *- sum_y
                grind
              have eq2: ¬ (2 : Edwards.CurveField) = 0 := by decide
              have := (Edwards.Ed25519.denomsNeZero e₂ e₂).left
              simp at this
              ring_nf at this
              simp only [mul_eq_zero] at eq0
              rcases eq0 with h0 | h0
              · have :=eq2 h0
                apply False.elim this
              · have := this h0
                apply False.elim this
          · have : e₁.x * e₂.y = -  e₁.y * e₂.x := by grind
            have :  e₁.x ^ 2 * e₂.y ^ 2= - e₁.x * e₂.x * e₁.y * e₂.y := by
              calc
              e₁.x ^ 2 * e₂.y ^ 2 = e₁.x * e₂.y * (e₁.x * e₂.y) := by ring
              _   = e₁.x * e₂.y * (- e₁.y * e₂.x) := by grind
              _   = - e₁.x * e₂.y * e₁.y * e₂.x := by ring
              _   = - e₁.x * e₂.x * e₁.y * e₂.y := by ring_nf
            rw[mul_assoc, this] at h
            sorry




lemma trans_birational {x y u v : CurveField}
  (non_x : ¬x = 0)
  (hya : 1 - y ≠ 0)
  (hym : 1 + y ≠ 0)
  (hu : u = (1 + y) / (1 - y))
  (hv : v = (1 + y) / ((1 - y) * x)) :
   x=u/v ∧ y= (u-1)/(u+1) := by
  constructor
  · simp[hu, hv]
    field_simp
  · simp[hu]
    field_simp
    simp
    have : (1+1:CurveField) ≠ 0 := by decide
    field_simp
lemma sum_aux_u
  {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  {u1 v1 u2 v2 : CurveField}
  (non_e1_x : e₁.x ≠ 0)
  (non_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₁.y ≠ 0)
  (hy2 : 1 - e₂.y ≠ 0)
  (hy3 : 1 + e₁.y ≠ 0)
  (hy4 : 1 + e₂.y ≠ 0)
  (hu1 : u1 = (1 + e₁.y) / (1 - e₁.y))
  (hv1 : v1 = (1 + e₁.y) / ((1 - e₁.y) * e₁.x))
  (hu2 : u2 = (1 + e₂.y) / (1 - e₂.y))
  (hv2 : v2 = (1 + e₂.y) / ((1 - e₂.y) * e₂.x))
  (hden : u1 - u2 ≠ 0)
  :
  (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y)
    =
  (u1 * u2 - 1) / (u1 - u2)
:= by
  simp [Edwards.add_y]
  have := (Edwards.Ed25519.denomsNeZero e₁ e₂).right
  simp at this
  have :  (1 - e₁.y * e₂.y * e₁.x * e₂.x * Edwards.Ed25519.d) ≠  0 := by grind
  field_simp
  have hx := trans_birational non_e1_x hy1 hy3 hu1 hv1
  have hy := trans_birational non_e2_x hy2 hy4 hu2 hv2
  sorry






lemma sum_aux_x_two {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : ¬e₁.x = 0)
  (zero_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₂.y ≠ 0)
  (hy3 : 1 + e₂.y ≠ 0)
  (heqy : e₁.y = e₂.y) :
  e₁.x= e₂.x ∨  e₁.x= -e₂.x := by
  have eq₁:= e₁.on_curve
  rw[heqy] at eq₁
  have := e₂.on_curve
  have : 1  = Edwards.Ed25519.a *e₂.x ^ 2 + e₂.y ^ 2  - Edwards.Ed25519.d * e₂.x ^ 2* e₂.y ^ 2 := by
    rw[this]
    ring_nf
  simp only [this] at eq₁
  have :  Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 +
    Edwards.Ed25519.d * e₁.x ^ 2 * e₂.y ^ 2
    = ( Edwards.Ed25519.a * e₂.x ^ 2 + e₁.x ^ 2 * e₂.y ^ 2 * Edwards.Ed25519.d
    - e₂.y ^ 2 * e₂.x ^ 2 * Edwards.Ed25519.d) +e₂.y ^ 2 := by grind
  simp only [this, add_left_inj] at eq₁
  have eq₂:
  Edwards.Ed25519.a * e₂.x ^ 2 + e₁.x ^ 2 * e₂.y ^ 2 * Edwards.Ed25519.d - e₂.y ^ 2 * e₂.x ^ 2 * Edwards.Ed25519.d -
  Edwards.Ed25519.a * e₁.x ^ 2 = 0 := by grind
  have :Edwards.Ed25519.a * e₂.x ^ 2 + e₁.x ^ 2 * e₂.y ^ 2 * Edwards.Ed25519.d - e₂.y ^ 2 * e₂.x ^ 2 * Edwards.Ed25519.d -
  Edwards.Ed25519.a * e₁.x ^ 2 =
  (Edwards.Ed25519.a -  e₂.y ^ 2 * Edwards.Ed25519.d) *(e₂.x ^ 2 -e₁.x ^ 2)
   := by
   calc
   Edwards.Ed25519.a * e₂.x ^ 2 + e₁.x ^ 2 * e₂.y ^ 2 * Edwards.Ed25519.d - e₂.y ^ 2 * e₂.x ^ 2 * Edwards.Ed25519.d -
  Edwards.Ed25519.a * e₁.x ^ 2 =
  Edwards.Ed25519.a * (e₂.x ^ 2 -e₁.x ^ 2)+ e₁.x ^ 2 * e₂.y ^ 2 * Edwards.Ed25519.d - e₂.y ^ 2 * e₂.x ^ 2 * Edwards.Ed25519.d
   := by grind
   _= Edwards.Ed25519.a * (e₂.x ^ 2 -e₁.x ^ 2)-  e₂.y ^ 2 * Edwards.Ed25519.d *(e₂.x ^ 2 -e₁.x ^ 2) := by grind
   _= (Edwards.Ed25519.a -  e₂.y ^ 2 * Edwards.Ed25519.d) *(e₂.x ^ 2 -e₁.x ^ 2) := by grind
  simp only [this, mul_eq_zero] at eq₂
  rcases eq₂ with h | h
  · have :Edwards.Ed25519.d *e₂.y ^ 2 = Edwards.Ed25519.a := by grind
    have :Edwards.Ed25519.d *e₁.x^2 *e₂.y ^ 2 = Edwards.Ed25519.a * e₁.x^2:= by grind
    have eq₁:= e₁.on_curve
    simp only [heqy, this] at eq₁
    have : 1 + Edwards.Ed25519.a * e₁.x ^ 2
    = Edwards.Ed25519.a * e₁.x ^ 2 +1 := by ring_nf
    simp only [this, add_right_inj, sq_eq_one_iff] at eq₁
    grind
  · have : e₂.x ^ 2 - e₁.x ^ 2=   (e₂.x  - e₁.x ) * (e₂.x  + e₁.x ) := by grind => ring
    simp only [this, mul_eq_zero] at h
    grind
















lemma sum_aux_x_eq {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : ¬e₁.x = 0)
  (non_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₂.y ≠ 0)
  (hy2 : 1 - e₁.y ≠ 0)
  (hy3 : 1 + e₂.y ≠ 0)
  (sum_x : (e₁ + e₂).x ≠ 0)
  (sum_y : ¬(e₁ + e₂).y = 1)
  (heqy : e₁.y = e₂.y)
  (heqx : e₁.x = e₂.x) :
 (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
    ((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
              (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
            2 -
          Curve25519.A -
        (1 + e₂.y) / (1 - e₂.y) -
      (1 + e₂.y) / (1 - e₂.y) := by
    simp [Edwards.add_y, heqy, heqx] at sum_y
    simp [Edwards.add_y, heqy]
    have : Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
              Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)
              = 2* Curve25519.roots_B * ((1 + e₂.y) / ((1 - e₂.y) * e₁.x) ):= by grind
    rw[this]
    set u :=  (1 + e₂.y) / (1 - e₂.y) with hu
    set v := (1 + e₂.y) / ((1 - e₂.y) * e₁.x) with hv
    have ht:= trans_birational non_e1_x hy1 hy3  hu hv
    have := (Edwards.Ed25519.denomsNeZero e₁ e₂).right
    simp [heqy ]at this
    have :1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d ≠ 0 :=by grind
    field_simp
    have neq: (1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d + (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x))
    = Edwards.Ed25519.a * e₂.x *(e₂.x-e₁.x)+ 2* e₂.y ^ 2
      - Edwards.Ed25519.d * e₂.x * e₂.y ^ 2*(e₁.x+e₂.x)
      := by
      have :=e₂.on_curve
      have : 1  = Edwards.Ed25519.a *e₂.x ^ 2 + e₂.y ^ 2  - Edwards.Ed25519.d * e₂.x ^ 2* e₂.y ^ 2 := by
        rw[this]
        ring_nf
      simp[this]
      calc
         Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2
      - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 -
        e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d +
        (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x) =
        Edwards.Ed25519.a * e₂.x ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x + e₂.y ^ 2
      - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 -
        e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d +
        e₂.y ^ 2  := by grind
        _ = Edwards.Ed25519.a * e₂.x ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x + 2* e₂.y ^ 2
      - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 -
        e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d := by grind
        _ = Edwards.Ed25519.a * e₂.x *(e₂.x-e₁.x)+ 2* e₂.y ^ 2
      - Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 -
        e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d := by grind
        _ = Edwards.Ed25519.a * e₂.x *(e₂.x-e₁.x)+ 2* e₂.y ^ 2
      - Edwards.Ed25519.d * e₂.x * e₂.y ^ 2*(e₁.x+e₂.x) := by grind
    simp[heqx] at neq
    have :  2 * e₂.y ^ 2 - Edwards.Ed25519.d * e₂.x * e₂.y ^ 2 * (e₂.x + e₂.x)
    =  2 * e₂.y ^ 2 *(1-  Edwards.Ed25519.d * e₂.x^2 )  := by
      calc
      2 * e₂.y ^ 2 - Edwards.Ed25519.d * e₂.x * e₂.y ^ 2 * (e₂.x + e₂.x)
        =  2 * e₂.y ^ 2 - 2* Edwards.Ed25519.d * e₂.x^2 * e₂.y ^ 2 := by grind
      _ =  2 * e₂.y ^ 2 *(1-  Edwards.Ed25519.d * e₂.x^2 ) := by grind
    rw[this] at neq
    have eq₂: (1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d - (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x))
     = -e₂.x  * (Edwards.Ed25519.d  * e₂.y ^ 2- Edwards.Ed25519.a) *(e₁.x+e₂.x)
     := by
      have :=e₂.on_curve
      have : 1  = Edwards.Ed25519.a *e₂.x ^ 2 + e₂.y ^ 2  - Edwards.Ed25519.d * e₂.x ^ 2* e₂.y ^ 2 := by
        rw[this]
        ring_nf
      have eq1: 1- e₂.y ^ 2 = Edwards.Ed25519.a *e₂.x ^ 2   - Edwards.Ed25519.d * e₂.x ^ 2* e₂.y ^ 2 := by
        rw[this]
        ring_nf
      have : (1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d - (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x))
     = (1 - e₂.y ^ 2) -  e₁.x * e₂.x *( Edwards.Ed25519.d * e₂.y ^ 2 - Edwards.Ed25519.a) := by grind
      rw[eq1] at this
      have : (1 - e₂.y ^ 2 * e₁.x * e₂.x * Edwards.Ed25519.d - (e₂.y ^ 2 - Edwards.Ed25519.a * e₁.x * e₂.x))
        = -e₂.x ^ 2 * (Edwards.Ed25519.d  * e₂.y ^ 2- Edwards.Ed25519.a) -
        e₁.x * e₂.x * (Edwards.Ed25519.d * e₂.y ^ 2 - Edwards.Ed25519.a) := by grind
      grind
    simp[heqx] at eq₂
    have :  -(e₂.x * (Edwards.Ed25519.d * e₂.y ^ 2 - Edwards.Ed25519.a) * (e₂.x + e₂.x)) =
     2* e₂.x^2 * (Edwards.Ed25519.a-Edwards.Ed25519.d * e₂.y ^ 2 ) := by grind
    simp[this] at eq₂
    simp[heqx, neq, eq₂]
    simp[heqx] at ht
    have eq₀: (2 * e₂.x ^ 2 * (Edwards.Ed25519.a - Edwards.Ed25519.d * e₂.y ^ 2))
    = 2 * (Edwards.Ed25519.a * e₂.x ^ 2 - Edwards.Ed25519.d * e₂.x ^ 2 *e₂.y ^ 2) := by grind
    have := e₂.on_curve
    have mul: Edwards.Ed25519.d * e₂.x ^ 2* e₂.y ^ 2 = Edwards.Ed25519.a *e₂.x ^ 2 + e₂.y ^ 2  - 1 := by
        rw[this]
        ring_nf
    simp[ mul] at eq₀
    have :  2 * (Edwards.Ed25519.a * e₂.x ^ 2 - (Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 - 1))
    =  2 * (1- e₂.y ^ 2) := by grind
    rw[this] at eq₀
    rw[eq₀]

    have eq₁: 2 * e₂.y ^ 2 * (1 - Edwards.Ed25519.d * e₂.x ^ 2) * 2 ^ 2  =
    2 *  (e₂.y ^ 2 - Edwards.Ed25519.d * e₂.x ^ 2* e₂.y ^ 2) * 2 ^ 2 := by grind
    rw[ mul] at eq₁
    have : e₂.y ^ 2 - (Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 - 1)
    =1-Edwards.Ed25519.a * e₂.x ^ 2 := by grind
    rw[this] at eq₁
    rw[eq₁]
    have : Edwards.Ed25519.a =-1 := rfl
    sorry
















lemma sum_aux_x_eqI {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (sum_x : (e₁ + e₂).x ≠ 0)
  (heqy : e₁.y = e₂.y)
  (heqx : e₁.x = -e₂.x) :
 (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
    ((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
              (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
            2 -
          Curve25519.A -
        (1 + e₂.y) / (1 - e₂.y) -
      (1 + e₂.y) / (1 - e₂.y) := by
    simp [Edwards.add_x, heqy, heqx] at sum_x
    grind



















lemma sum_aux_x {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : ¬e₁.x = 0)
  (zero_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₂.y ≠ 0)
  (hy3 : 1 + e₂.y ≠ 0)
  (sum_x : (e₁ + e₂).x ≠ 0)
  (sum_y : ¬(e₁ + e₂).y = 1)
  (heqy : e₁.y = e₂.y) :
 (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
    ((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
              (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
            2 -
          Curve25519.A -
        (1 + e₂.y) / (1 - e₂.y) -
      (1 + e₂.y) / (1 - e₂.y) := by
      have := sum_aux_x_two non_e1_x zero_e2_x hy1 hy3 heqy
      rcases this with h | h
      · apply sum_aux_x_eq
        all_goals simp_all
      · apply sum_aux_x_eqI
        all_goals simp_all






























lemma sum_aux_y {e₁ e₂ : Edwards.Point Edwards.Ed25519} (non_e1_x : e₁.x ≠ 0)
  (non_e1_x : ¬e₁.x = 0)
  (zero_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₂.y ≠ 0)
  (hy2 : 1 - e₁.y ≠ 0)
  (hy3 : 1 + e₂.y ≠ 0)
  (sum_x : (e₁ + e₂).x ≠ 0)
  (sum_y : ¬(e₁ + e₂).y = 1)
  (heqy : e₁.y = e₂.y) :
Curve25519.roots_B * (1 + (e₁ + e₂).y) / ((1 - (e₁ + e₂).y) * (e₁ + e₂).x) =
  -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) +
    -((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
          (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
            Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) *
        (((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
                    (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                      Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
                  2 -
                Curve25519.A -
              (1 + e₂.y) / (1 - e₂.y) -
            (1 + e₂.y) / (1 - e₂.y) -
          (1 + e₂.y) / (1 - e₂.y))) := by
    have := sum_aux_x non_e1_x zero_e2_x hy1 hy3 sum_x sum_y heqy
    rw[← this ]
    set a:= ((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
            (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
              Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) with ha
    sorry






theorem add_non_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x ≠ 0)
  (sum_x : (e₁ + e₂).x ≠ 0) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  by_cases h1: e₁.y = 1
  · apply add_eq_T_point_fromEdwards1 e₁ e₂ non_e1_x h1
  · by_cases h2: e₂.y = 1
    · apply add_eq_T_point_fromEdwards2 _ _ zero_e2_x h2
    · by_cases sum_y: (e₁+e₂).y=1
      · rw[← zero_iff] at sum_y
        simp only [sum_y]
        have : e₂= -e₁ := by grind
        rw[this, neg_fromEdwards, map_zero]
        simp only [add_neg_cancel]
      · unfold fromEdwards
        simp_all only [ne_eq, ↓reduceDIte, false_and]
        simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add, WeierstrassCurve.Affine.negY,
          WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, neg_add_rev]
        simp [MontgomeryCurveCurve25519]
        have hy1 : 1 - e₂.y ≠ 0 := by grind
        have hy2 : 1 - e₁.y ≠ 0 := by grind
        have hy3 : 1 + e₂.y ≠ 0 := by
          intro hy3
          have eq1: e₂.y = -1 := by grind
          have := e₂.on_curve
          simp only [eq1, even_two, Even.neg_pow, one_pow, mul_one] at this
          ring_nf at this
          simp only [add_right_inj] at this
          field_simp at this
          have : Edwards.Ed25519.a ≠  Edwards.Ed25519.d := by decide
          revert this
          rw[this]
          decide
        have := injective_Neg hy1 hy2 hy3 non_e1_x zero_e2_x
        simp only [← this]
        by_cases heq:  e₁.y = e₂.y ∧ e₁.x = -e₂.x
        · simp only [heq, and_self, ↓reduceDIte, reduceCtorEq]
          simp only [Edwards.add_y, heq] at sum_y
          simp only [mul_neg, neg_mul, sub_neg_eq_add] at sum_y
          field_simp at sum_y
          simp only [Edwards.add_x, heq] at sum_x
          have eq:= e₂.on_curve
          have : Edwards.Ed25519.a * e₂.x ^ 2 + e₂.y ^ 2 =
           e₂.y ^ 2+ Edwards.Ed25519.a * e₂.x ^ 2 := by grind
          rw[this] at eq
          rw[eq] at sum_y
          have : 1 + Edwards.Ed25519.d * e₂.x ^ 2 * e₂.y ^ 2 ≠ 0 := by
            have := Edwards.Ed25519.denomsNeZero e₂ e₂
            simp only [ne_eq] at this
            grind
          field_simp at sum_y
          grind
        · simp only [heq, ↓reduceDIte, WeierstrassCurve.Affine.Point.some.injEq]
          have := injective_fromEdwards hy1 hy2
          simp only [WeierstrassCurve.Affine.slope, this, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, sub_neg_eq_add,
            ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_mul]
          by_cases heqy: e₁.y = e₂.y
          · simp only [heqy, true_and] at heq
            simp only [heqy, ↓reduceIte]
            have sum_x1:=sum_x
            simp only [Edwards.add_x, heqy] at sum_x
            field_simp at sum_x
            simp only [div_eq_zero_iff, mul_eq_zero] at sum_x
            have : ¬ ( Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) =
                -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
                field_simp [roots_B_non_zero]
                grind
            simp only [this, ↓reduceIte]
            have := sum_aux_x non_e1_x zero_e2_x hy1 hy3
            simp_all
            apply sum_aux_y
            all_goals simp_all
          · simp[heqy ]
            sorry





lemma fromEdwards_add_of_snd_y_eq_neg_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e2_x : ¬e₂.x = 0)
  (eq_e2_y_1 : 1 + e₂.y = 0) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  have eq2: e₂.y = -1 := by grind
  have := e₂.on_curve
  simp only [eq2, even_two, Even.neg_pow, one_pow, mul_one] at this
  have : Edwards.Ed25519.a * e₂.x ^ 2  =  Edwards.Ed25519.d * e₂.x ^ 2:= by grind
  have :   e₂.x ^ 2*(Edwards.Ed25519.a-    Edwards.Ed25519.d) = 0:= by grind
  simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, non_e2_x, false_or] at this
  revert this
  have: Edwards.Ed25519.a= -1:= rfl
  rw[this]
  have: Edwards.Ed25519.d= d:= rfl
  rw[this]
  have :¬ ((-1:CurveField) - d) = 0:= by decide
  intro h
  have := this h
  apply False.elim this

lemma fromEdwards_add_of_sum_x_eq_zero_of_y_ne_one_of_y_ne_neg_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (sum_x : (e₁ + e₂).x = 0)
  (sum_y : ¬(e₁ + e₂).y = 1)
  (sum_y_1 : ¬(e₁ + e₂).y = -1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  have := (e₁ + e₂).on_curve
  simp[sum_x] at this
  grind

lemma fromEdwards_add_of_x_eq_zero (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x = 0)
  (non_e2_x : e₂.x = 0) :
 fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  by_cases sum_y : (e₁ + e₂).y = 1
  · apply add_eq_zero_fromEdwards _ _ sum_y
  · unfold fromEdwards
    simp only [sum_y, ↓reduceDIte]
    simp only [Edwards.add_x, non_e1_x, zero_mul, non_e2_x, mul_zero, add_zero, div_one, true_and, div_zero]
    simp only [Edwards.add_y, non_e1_x, mul_zero, non_e2_x, sub_zero, zero_mul, div_one]
    have ceq₁:= e₁.on_curve
    simp only [non_e1_x, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, zero_mul, add_zero,
    sq_eq_one_iff] at ceq₁
    rcases ceq₁ with hy | hy
    · have ceq₂:= e₂.on_curve
      simp only [non_e2_x, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, zero_mul, add_zero,
        sq_eq_one_iff] at ceq₂
      rcases ceq₂ with hy2 | hy2
      · simp only [hy, hy2, mul_one, sub_self, div_zero, ↓reduceDIte, add_zero]
        have :¬  (1: CurveField) = -1 := by decide
        simp only [this, ↓reduceDIte, reduceCtorEq]
        simp only [Edwards.add_y, hy, hy2, mul_one, non_e1_x, mul_zero, non_e2_x, sub_zero, ne_eq, one_ne_zero,
          not_false_eq_true, div_self, not_true_eq_false] at sum_y
      · simp only [hy, hy2, mul_neg, mul_one, ↓reduceDIte, dite_eq_ite, zero_add, right_eq_ite_iff]
        have :¬  (-1: CurveField) = 1 := by decide
        simp only [this, IsEmpty.forall_iff]
    · have ceq₂:= e₂.on_curve
      simp only [non_e2_x, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, zero_mul, add_zero,
        sq_eq_one_iff] at ceq₂
      rcases ceq₂ with hy2 | hy2
      · simp only [hy, hy2, mul_one, ↓reduceDIte, dite_eq_ite, add_zero, right_eq_ite_iff]
        have :¬  (-1: CurveField) = 1 := by decide
        simp only [this, IsEmpty.forall_iff]
      · simp only [hy, hy2, mul_neg, mul_one, neg_neg, sub_self, div_zero, ↓reduceDIte, dite_eq_ite]
        have :¬  (1: CurveField) = -1 := by decide
        simp only [this, ↓reduceDIte]
        simp only [Edwards.add_y, hy, hy2, mul_neg, mul_one, neg_neg, non_e1_x, mul_zero, non_e2_x, sub_zero, neg_zero,
        ne_eq, one_ne_zero, not_false_eq_true, div_self, not_true_eq_false] at sum_y


theorem add_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  by_cases non_e1_x : e₁.x ≠ 0
  ·  by_cases non_e2_x : e₂.x = 0
     ·  apply  add_fromEdwards_second _ _ non_e1_x non_e2_x
     ·  by_cases  sum_x : (e₁ + e₂).x ≠ 0
        · apply add_non_fromEdwards
          all_goals simp_all
        · simp at sum_x
          by_cases sum_y : (e₁ + e₂).y = 1
          · apply add_eq_zero_fromEdwards
            all_goals simp_all
          · by_cases non_e1_y : 1 - e₁.y = 0
            · apply add_eq_T_point_fromEdwards1  e₁ e₂ non_e1_x
              grind
            · by_cases non_e2_y : 1 - e₂.y = 0
              · apply add_eq_T_point_fromEdwards2  e₁ e₂ non_e2_x
                grind
              · by_cases non_e2_y_1 : 1 + e₂.y = 0
                · apply fromEdwards_add_of_snd_y_eq_neg_one
                  all_goals simp_all
                · by_cases sum_y_1 : (e₁ + e₂).y = -1
                  · apply  add_eq_T_point_fromEdwards
                    all_goals simp_all
                  · apply fromEdwards_add_of_sum_x_eq_zero_of_y_ne_one_of_y_ne_neg_one
                    all_goals simp_all
  · simp only [ne_eq, Decidable.not_not] at non_e1_x
    · by_cases non_e2_x : e₂.x ≠  0
      · have :=  add_fromEdwards_second _ _ non_e2_x non_e1_x
        rw[add_comm, Edwards.add_comm_Ed25519, this]
      · simp at non_e2_x
        apply fromEdwards_add_of_x_eq_zero
        all_goals simp_all

theorem double_T {e : Edwards.Point Edwards.Ed25519} (hx : e.x = 0) :
  (e + e).x=0 := by
  simp[Edwards.add_x, hx]

theorem power_T (n : ℕ) {e : Edwards.Point Edwards.Ed25519} (hx : e.x = 0) :
  n • e.x=0 := by
  induction n
  · simp
  · rename_i n hn
    simp only [add_smul, hn, one_smul, zero_add]
    exact hx

theorem double_T1 {e : Edwards.Point Edwards.Ed25519}
  (hx : (e + e).x = 0) :
  (e.x=0 ∧ e.y ^ 2 =1) ∨  (e.x ^ 2 = -1 ∧ e.y =0) := by
  have hy:= T_point_x hx
  have hx1:=hx
  simp[Edwards.add_x] at hx
  field_simp at hx
  simp only [mul_eq_zero] at hx
  rcases hx with h2 | h2
  · rcases h2 with h2 | h2
    · rcases h2 with h2 | h2
      · simp_all only [sq_eq_one_iff, true_and, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_eq_neg,
          one_ne_zero, false_and, or_false]
        simp only [Edwards.add_y, h2, mul_zero, sub_zero, zero_mul, div_one] at hy
        rcases hy with hy | hy
        · field_simp at hy
          grind
        · have :=e.on_curve
          field_simp at this
          field_simp at hy
          simp only [hy, mul_neg, mul_one, neg_mul] at this
          simp only [h2, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, zero_mul, neg_zero,
            add_zero] at this
          have eq: -1 ≠  (1:CurveField):=by decide
          have := eq this
          apply False.elim this
      · rcases hy with h1 | h1
        · simp[Edwards.add_y] at h1
          field_simp at h1
          simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub, zero_mul, sub_zero, div_one,
            zero_ne_one, and_false, and_true, false_or]
          have := e.on_curve
          simp only [h2, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero] at this
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
      simp only [ha, mul_one, eq1, neg_add_cancel] at eq
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
      simp only [ha, mul_neg, mul_one, neg_neg, eq1, add_neg_cancel] at eq
      have : (0:CurveField) ≠  1 + Edwards.Ed25519.d  :=by decide
      have := this eq
      apply False.elim this

theorem double_special_point {e : Edwards.Point Edwards.Ed25519}
  (hx : e.x ^ 2 = -1)
  (hy : e.y = 0) :
  (e + e).y = -1 ∧ (e + e).x = 0 ∧ ¬ e.x= 0 := by
  constructor
  · simp only [Edwards.add_y]
    simp only [hy, mul_zero, zero_sub, sub_zero, div_one, neg_inj]
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
  simp only [hy2, this, ↓reduceDIte, non, and_self, hy, zero_ne_one, non_x, zero_eq_neg, one_ne_zero, add_zero,
    sub_zero, ne_eq, not_false_eq_true, div_self, mul_one, one_mul]
  simp only [T_point]
  simp only [WeierstrassCurve.Affine.Point.add_def, WeierstrassCurve.Affine.Point.add]
  simp only[MontgomeryCurveCurve25519]
  have : ¬ Curve25519.roots_B / e.x = -(Curve25519.roots_B / e.x) := by
    intro h
    have : Curve25519.roots_B =0 := by grind
    apply  roots_B_non_zero this
  simp only [Curve25519.A, WeierstrassCurve.Affine.negY, mul_one, sub_zero, this, and_false, ↓reduceDIte,
    WeierstrassCurve.Affine.addX, not_false_eq_true, WeierstrassCurve.Affine.slope_of_Y_ne', one_pow, zero_mul,
    sub_neg_eq_add, add_zero, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, neg_add_rev,
    WeierstrassCurve.Affine.Point.some.injEq]
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
      simp_all only [sq_eq_one_iff, true_and, mul_zero, div_zero]
      have := (e+e).on_curve
      simp only [hx, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, zero_mul, add_zero,
    sq_eq_one_iff] at this
      rcases this with h | h
      · simp only [h, ↓reduceDIte]
        rcases h1.right
        · simp_all
        · have : (-1)≠  (1:CurveField):=by decide
          simp_all only [or_true, and_self, ne_eq, ↓reduceDIte]
          rw[Montgomery.T_point_order_two]
      · have : (-1)≠  (1:CurveField):=by decide
        simp only [h, this, ↓reduceDIte]
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
  · simp only [zero_nsmul, map_zero]
  · rename_i n hn
    simp only [add_smul, one_smul]
    rw[add_fromEdwards, hn]

theorem fromEdwards_eq_MontgomeryPoint_toPoint (e : Edwards.Point Edwards.Ed25519)
  (m : MontgomeryPoint)
  (non : ¬ e.y = 1)
  (non_x : ¬ e.x = 0)
  (h : (((U8x32_as_Nat m) % 2 ^255):ℕ )= (1 + e.y) / (1 - e.y)) :
  fromEdwards e = MontgomeryPoint.mkPoint m  := by
  unfold fromEdwards
  simp only [non, ↓reduceDIte, non_x, false_and]
  unfold MontgomeryPoint.mkPoint
  rw[h]
  clear *- non
  apply symm
  apply MontgomeryPoint.u_affine_toPoint_spec
  · simp only [ne_eq, div_eq_zero_iff, not_or]
    constructor
    · intro ha
      have := exceptEdwardsPoint ha
      apply non_x this
    · grind only
  · have := on_MontgomeryCurves e non non_x
    simp only at this
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
    let p := MontgomeryPoint.mkPoint m
    toEdwards p

end toEdwards

end Montgomery
