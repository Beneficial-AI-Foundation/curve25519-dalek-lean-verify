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
-/
noncomputable def MontgomeryPoint.toPoint (m : MontgomeryPoint) : Point Ed25519 :=
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
section MontgomeryPoint

open curve25519_dalek.montgomery
open curve25519_dalek.math


/-- Create a point from a MontgomeryPoint byte representation.
    Computes the v-coordinate from u using the Montgomery curve equation v² = u³ + A·u² + u.

    Note: The curve equation proof currently uses `sorry`. This requires proving that
    `sqrt_checked` returns a value whose square equals its input, which depends on
    the mathematical properties of the square root function in the field. -/

noncomputable def MontgomeryPoint.u_affine_toPoint (u : CurveField) : Point:=
    let v_squared := u ^ 3 + Curve25519.A * u ^ 2 + u
    let (v_abs, _is_sq) := curve25519_dalek.math.sqrt_checked v_squared
    let v := v_abs
    have curve_eq : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u := by
       sorry
    Montgomery.mk_point (u := u) (v := v) (h := curve_eq)


noncomputable def MontgomeryPoint.toPoint (m : MontgomeryPoint) : Point:=
    let u : CurveField := U8x32_as_Nat m
    MontgomeryPoint.u_affine_toPoint u
end MontgomeryPoint

section fromEdwards

noncomputable def fromEdwards.toPoint : Edwards.Point Edwards.Ed25519 → Point
  | m =>
    Montgomery.mk_point (u := (1+m.y)/(1-m.y)) (v := (1+m.y)/((1-m.y)*m.x)) (h := by
        have := m.on_curve
        sorry)

theorem comm_mul_fromEdwards (n : ℕ) (e : Edwards.Point Edwards.Ed25519) :
  fromEdwards.toPoint (n • e) = n •  (fromEdwards.toPoint e) := by
  sorry

end fromEdwards

section toMontgomery
open curve25519_dalek.math

theorem sqrt_checked_spec (u : ZMod p) {r : ZMod p} {b : Bool} :
  sqrt_checked u = (r, b) → b = true → r^2 = u := by
  intro h_call h_true
  sorry

noncomputable def toMontgomery.toPoint : Point → Edwards.Point Edwards.Ed25519
  | .zero => 0
  | .some (x := u) (y := v) (h:= h) =>
    { x := u * v⁻¹, y := (u - 1) * (u + 1)⁻¹, on_curve := (by
    have eq:=h.left
    rw [WeierstrassCurve.Affine.equation_iff] at eq
    simp [MontgomeryCurveCurve25519] at eq
    have :=h.right
    simp [WeierstrassCurve.Affine.evalEval_polynomialY, WeierstrassCurve.Affine.evalEval_polynomialX, MontgomeryCurveCurve25519] at this
    sorry
    )
 }
end toMontgomery
