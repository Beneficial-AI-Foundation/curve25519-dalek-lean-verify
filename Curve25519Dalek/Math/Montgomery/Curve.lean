/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Affine Montgomery Curve Points for Curve25519

This file defines affine point arithmetic on Montgomery curves,
focusing on the affine coordinate representation (u, v).

## Contents

1. **Field Definitions**: `CurveField` as `ZMod p` where p = 2^255 - 19
2. **Affine Point Structure**: Points (u, v) satisfying v² = u³ + A·u² + u
3. **Group Law**: Addition formulas and group structure for affine points
from Mathlib EllipticCurve.Affine.Point

## References

* Costello, Craig and Smith, Benjamin: "Montgomery curves and their arithmetic" (2017)
  https://eprint.iacr.org/2017/212.pdf
* Bernstein, Daniel J.: "Curve25519: new Diffie-Hellman speed records" (2006)
  https://cr.yp.to/ecdh/curve25519-20060209.pdf
-/

namespace Montgomery

open ZMod

/-! ## Mathematical Foundations -/

/-- The finite field F_p where p = 2^255 - 19. -/
abbrev CurveField : Type := ZMod p

instance : Fact (Nat.Prime p) := ⟨PrimeCert.prime_25519''⟩

instance : NeZero (2 : CurveField) := ⟨by decide⟩

-- Enable decidable equality for the field (required for mathlib's AddCommGroup instance)
open scoped Classical in
noncomputable instance : DecidableEq CurveField := inferInstance

/-- Helper lemma for modular arithmetic lifting -/
theorem lift_mod_eq (a b : ℕ) (h : a % p = b % p) : (a : CurveField) = (b : CurveField) := by
  exact (ZMod.natCast_eq_natCast_iff a b p).mpr h

/-- A Montgomery curve structure defined by parameters A and B.
    The curve equation is: B·v² = u³ + A·u² + u -/
def Curve25519.A := (486662 : CurveField)

def MontgomeryCurveCurve25519 : WeierstrassCurve.Affine CurveField :=
  { a₁ := 0
    a₂ := (486662 : CurveField)
    a₃ := 0
    a₄ := 1
    a₆ := 0 }

abbrev Point :=  MontgomeryCurveCurve25519.Point

lemma zero_def : (0 : Point) = .zero := rfl

def T_point : Point := .some (x := 0) (y := 0) (h := by
  constructor
  · norm_num [MontgomeryCurveCurve25519]
  · left
    norm_num [MontgomeryCurveCurve25519])

theorem non_singular {u v : CurveField}
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    v ≠ 0 ∨ 3 * u ^ 2 + 2 * Curve25519.A * u + 1 ≠ 0  := by
    by_cases hv: v =0
    · right
      simp[hv] at h
      have :  u ^ 3 + Curve25519.A * u ^ 2 + u = u *( u ^ 2 + Curve25519.A * u  + 1) := by ring
      rw[this] at h
      have := mul_eq_zero.mp h.symm
      rcases this with h1 | h1
      · simp[h1]
      · have : 3 * u ^ 2 + 2 * Curve25519.A * u + 1=
        3 * (u ^ 2 +  Curve25519.A * u + 1) - Curve25519.A * u -2 := by ring
        rw[this, h1]
        simp
        intro h2
        have : Curve25519.A * u = -2 := by grind
        simp[this] at h1
        have eq1: Curve25519.A^2 * u^2 = 4 := by grind
        have : -2 + (1:CurveField)= -1 := by ring
        rw[add_assoc, this] at h1
        have :  Curve25519.A ^ 2 * u^2 + Curve25519.A ^ 2* (-1) = 0  := by grind
        rw[eq1, Curve25519.A] at this
        revert this
        decide
    · simp[hv]

/-- Create a point from coordinates with curve equation proof and nonsingular condition. -/
def mk_point (u v : CurveField)
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u := by grind) :
    Point :=
  .some (x := u) (y := v) (h := by
    constructor
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp only [MontgomeryCurveCurve25519]
      rw [Curve25519.A] at h
      linear_combination h
    · have hns := non_singular h
      rcases hns with hv | hu
      · right
        rw [WeierstrassCurve.Affine.evalEval_polynomialY]
        simp only [MontgomeryCurveCurve25519]
        intro h0
        apply hv
        have : (2 : CurveField) * v = 0 := by
          convert h0 using 1
          ring
        exact (mul_eq_zero.mp this).resolve_left (NeZero.ne 2)
      · left
        rw [WeierstrassCurve.Affine.evalEval_polynomialX]
        simp only [MontgomeryCurveCurve25519]
        intro h0
        apply hu
        rw [Curve25519.A]
        linear_combination -h0)

/-- Extract u-coordinate from a point. -/
def get_u : Point → CurveField
  | .zero => 0
  | .some (x := u) .. => u

def get_v : Point → CurveField
  | .zero => 0
  | .some (y := v) .. => v

@[simp] theorem get_u_zero : get_u (0: Point) = 0 := rfl
@[simp] theorem get_v_zero : get_v (0: Point) = 0 := rfl

@[simp] theorem get_u_T : get_u T_point = 0 := rfl
@[simp] theorem get_v_T : get_v T_point = 0 := rfl

@[simp] theorem neg_u_coord (P : Point) :
    get_u (-P) = get_u P := by cases P <;> rfl

@[simp] theorem neg_v_coord (P : Point) :
    get_v (-P) = -(get_v P) := by
  cases P
  · rfl
  · simp [get_v, MontgomeryCurveCurve25519]

/-! ### Group Law Properties -/

/-- Addition is commutative for points.
This follows directly from mathlib's AddCommGroup instance for Weierstrass curve points. -/
theorem add_comm (P Q : Point) : P + Q = Q + P :=
  AddCommGroup.add_comm P Q

theorem uADD (P Q : Point)
  (PZero : P ≠ 0) (QZero : Q ≠ 0)
  (nPT : P ≠ T_point) (nQT : Q ≠ T_point)
  (PQ : P ≠ Q) :
  get_u (P + Q) * get_u (P - Q) * (get_u P - get_u Q)^2  = (get_u P * get_u Q - 1)^2 := by
  sorry

theorem uDBL (P : Point) (PZero : P ≠ 0) (nPT : P ≠ T_point) :
  4 * get_u (2 • P) * get_u (P) * ((get_u P)^2 +  Curve25519.A * get_u P + 1) = ((get_u P) ^ 2 - 1)^2 := by
  sorry

/-- Addition is associative for points.
This follows directly from mathlib's AddCommGroup instance for Weierstrass curve points. -/
theorem add_assoc' (P Q R : Point) : (P + Q) + R = P + (Q + R) :=
  add_assoc P Q R

end Montgomery
