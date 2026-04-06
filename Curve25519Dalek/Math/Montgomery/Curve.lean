/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
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
open WeierstrassCurve.Affine.Point

/-! ## Mathematical Foundations -/

/-- The finite field F_p where p = 2^255 - 19. -/
abbrev CurveField : Type := ZMod p

instance : Fact (Nat.Prime p) := ⟨PrimeCert.prime_25519''⟩

instance : NeZero (2 : CurveField) := ⟨by decide⟩

-- Enable decidable equality for the field (required for mathlib's AddCommGroup instance)
open scoped Classical in
noncomputable instance : DecidableEq CurveField := inferInstance

theorem lift_mod_eq_iff (a b : ℕ) : (a ≡ b [MOD p]) ↔ (a : CurveField) = (b : CurveField) := by
  rw [Nat.ModEq]
  exact (ZMod.natCast_eq_natCast_iff a b p).symm

theorem lift_mod_add (a b : ℕ) : (a : CurveField) + (b : CurveField) = ((a + b) : CurveField) := by
  rfl

theorem lift_mod_mul (a b : ℕ) :
    (a : CurveField) * (b : CurveField) = ((a * b) : CurveField) := by rfl

theorem mod_nat_mul_mod (a b : ℕ) : (a) * (b % p) ≡ a * b [MOD p] := by
  exact ((Nat.mod_modEq b p).mul_left (a))

/-- A Montgomery curve structure defined by parameters A and B.
    The curve equation is: B·v² = u³ + A·u² + u -/
def Curve25519.A := (486662 : CurveField)

def MontgomeryCurveCurve25519 : WeierstrassCurve.Affine CurveField :=
  { a₁ := 0
    a₂ := Curve25519.A
    a₃ := 0
    a₄ := 1
    a₆ := 0 }

abbrev Point := MontgomeryCurveCurve25519.Point

lemma zero_def : (0 : Point) = .zero := rfl

def T_point : Point := .some (x := 0) (y := 0) (h := by
  constructor
  · norm_num [MontgomeryCurveCurve25519]
  · left
    norm_num [MontgomeryCurveCurve25519, Curve25519.A])

theorem T_point_order_two : T_point + T_point = 0 := by
  unfold T_point
  simp [MontgomeryCurveCurve25519]

theorem non_singular {u v : CurveField}
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    v ≠ 0 ∨ 3 * u ^ 2 + 2 * Curve25519.A * u + 1 ≠ 0 := by
  by_cases hv : v = 0
  · right
    simp only [hv, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    have : u ^ 3 + Curve25519.A * u ^ 2 + u = u * (u ^ 2 + Curve25519.A * u + 1) := by ring
    rw [this] at h
    have := mul_eq_zero.mp h.symm
    rcases this with h1 | h1
    · simp [h1]
    · have : 3 * u ^ 2 + 2 * Curve25519.A * u + 1 =
      3 * (u ^ 2 + Curve25519.A * u + 1) - Curve25519.A * u - 2 := by ring
      rw [this, h1]
      simp only [mul_zero, zero_sub, ne_eq]
      intro h2
      have : Curve25519.A * u = -2 := by grind
      simp only [this] at h1
      have eq1: Curve25519.A^2 * u^2 = 4 := by grind
      have : -2 + (1 : CurveField) = -1 := by ring
      rw [add_assoc, this] at h1
      have : Curve25519.A ^ 2 * u^2 + Curve25519.A ^ 2 * (-1) = 0 := by grind
      rw [eq1, Curve25519.A] at this
      revert this
      decide
  · simp [hv]

lemma nonsingular_iff (x y : CurveField) :
    MontgomeryCurveCurve25519.Nonsingular x y ↔ MontgomeryCurveCurve25519.Equation x y := by
  simp only [MontgomeryCurveCurve25519, WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff, zero_mul, add_zero, one_mul, ne_eq, sub_zero,
    and_iff_left_iff_imp]
  intro h
  rcases non_singular h
  · right
    rename_i h1
    intro a
    apply h1
    have : (2 : CurveField) * y = 0 := by
      rw [two_mul]
      grind
    exact (mul_eq_zero.mp this).resolve_left (NeZero.ne 2)
  · left
    rename_i h1
    grind

/-- Create a point from coordinates with curve equation proof and nonsingular condition. -/
def mk_point {u v : CurveField}
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u := by grind) :
    Point :=
  .some ((nonsingular_iff u v).mpr (by
        rw [WeierstrassCurve.Affine.equation_iff]
        simp only [MontgomeryCurveCurve25519]
        simp [h]))

theorem ext (u v x y : CurveField) (equx : u = x) (eqvy : v = y)
    (huv : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u)
    (hxy : y ^ 2 = x ^ 3 + Curve25519.A * x ^ 2 + x) :
    mk_point huv = mk_point hxy := by
  unfold mk_point; simp [equx,eqvy]

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

/-- The coordinates of a non-zero point satisfy the curve equation. -/
theorem point_on_curve (P : Point) (hP : P ≠ 0) :
    get_v P ^ 2 = get_u P ^ 3 + Curve25519.A * get_u P ^ 2 + get_u P := by
  cases P with
  | zero => contradiction
  | some hpoint =>
    unfold get_u get_v Curve25519.A
    simp only []
    have h_eq := hpoint.1
    rw [WeierstrassCurve.Affine.equation_iff] at h_eq
    simp only [MontgomeryCurveCurve25519] at h_eq
    ring_nf at h_eq ⊢
    exact h_eq

theorem mk_point_def (P : Point) (hP : P ≠ 0) :
    P = mk_point (point_on_curve P hP) := by
  cases P
  · contradiction
  · unfold mk_point
    simp

theorem get_u_v_inj (P Q : Point) (nonP : P ≠ 0) (nonQ : Q ≠ 0)
    (hu : get_u P = get_u Q) (hv : get_v P = get_v Q) :
    P = Q := by
  cases P
  · simp [zero_def] at nonP
  · cases Q
    · simp [zero_def] at nonQ
    · unfold get_u at hu
      unfold get_v at hv
      simp_all

theorem get_u_v_inj_neg (P Q : Point) (nonP : P ≠ 0) (nonQ : Q ≠ 0)
    (hu : get_u P = get_u Q) (hv : get_v P = -get_v Q) :
    P = -Q := by
  cases P
  · simp [zero_def] at nonP
  · cases Q
    · simp [zero_def] at nonQ
    · unfold get_u at hu
      unfold get_v at hv
      simp_all [MontgomeryCurveCurve25519]

theorem mk_point_T {P : Point} (hP : P ≠ 0) (hu : get_u P = 0) (hv : get_v P = 0) :
    P = T_point := by
  unfold T_point
  rcases P
  · simp [zero_def] at hP
  · simp only [some.injEq]
    unfold get_u at hu
    unfold get_v at hv
    simp_all

theorem mk_point_neq_zero {u v : CurveField} (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    mk_point h ≠ 0 := by unfold mk_point; simp

@[simp] theorem get_u_mk_point {u v : CurveField}
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    get_u (mk_point h) = u := rfl

@[simp] theorem get_v_mk_point {u v : CurveField}
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    get_v (mk_point h) = v := rfl

@[simp] theorem mk_point_neq_T_of_u {u v : CurveField}
    (hu : u ≠ 0)
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    (mk_point h) ≠ T_point := by
  unfold mk_point T_point
  simp [hu]

@[simp] theorem mk_point_neq {u₁ v₁ u₂ v₂ : CurveField}
    (hu : u₁ ≠ u₂)
    (h₁ : v₁ ^ 2 = u₁ ^ 3 + Curve25519.A * u₁ ^ 2 + u₁)
    (h₂ : v₂ ^ 2 = u₂ ^ 3 + Curve25519.A * u₂ ^ 2 + u₂) :
    (mk_point h₁) ≠ (mk_point h₂) := by
  unfold mk_point
  simp [hu]

@[simp] theorem mk_point_neq_neg {u₁ v₁ u₂ v₂ : CurveField}
    (hu : u₁ ≠ u₂)
    (h₁ : v₁ ^ 2 = u₁ ^ 3 + Curve25519.A * u₁ ^ 2 + u₁)
    (h₂ : v₂ ^ 2 = u₂ ^ 3 + Curve25519.A * u₂ ^ 2 + u₂) :
    (mk_point h₁) ≠ (-mk_point h₂) := by
  unfold mk_point
  simp [hu]

/-! ### Group Law Properties -/

/-- Addition is commutative for points.
This follows directly from mathlib's AddCommGroup instance for Weierstrass curve points. -/
theorem add_comm (P Q : Point) : P + Q = Q + P :=
  AddCommGroup.add_comm P Q

theorem uADD (P Q : Point)
    (PZero : P ≠ 0) (QZero : Q ≠ 0)
    (nPT : P ≠ T_point) (nQT : Q ≠ T_point)
    (PQ : P ≠ Q) (PQ : P ≠ -Q) :
    get_u (P + Q) * get_u (P - Q) * (get_u P - get_u Q)^2  = (get_u P * get_u Q - 1)^2 := by
  unfold get_u
  rcases P
  · simp only [zero_def, ne_eq, not_true_eq_false] at PZero
  · rename_i x₁ y₁ nonS₁ nonP
    rcases Q
    · simp only [zero_def, ne_eq, not_true_eq_false] at QZero
    · rename_i x₂ y₂ nonS₂
      have hxy : ¬(x₁ = x₂ ∧ y₁ = MontgomeryCurveCurve25519.negY x₂ y₂) := by
        simp only [MontgomeryCurveCurve25519, neg_some, WeierstrassCurve.Affine.negY, zero_mul,
          sub_zero, ne_eq, some.injEq, not_and] at PQ
        simp only [WeierstrassCurve.Affine.negY, MontgomeryCurveCurve25519, zero_mul, sub_zero,
          not_and]
        exact PQ
      have := @WeierstrassCurve.Affine.Point.add_some CurveField _ MontgomeryCurveCurve25519 _
          x₁ x₂ y₁ y₂ hxy nonS₁ nonS₂
      simp only [MontgomeryCurveCurve25519, this, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY, zero_mul, sub_zero,
        sub_neg_eq_add, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_ite, mul_zero, ite_self, add_zero, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, ite_mul, neg_add_rev]
      have : WeierstrassCurve.Affine.Point.some nonS₁ -
          WeierstrassCurve.Affine.Point.some nonS₂ =
          WeierstrassCurve.Affine.Point.some nonS₁ +
          -WeierstrassCurve.Affine.Point.some nonS₂ := sub_eq_add_neg _ _
      rw [this, neg_some]
      have hxy_neg : ¬(x₁ = x₂ ∧
          y₁ = MontgomeryCurveCurve25519.negY x₂ (MontgomeryCurveCurve25519.negY x₂ y₂)) := by
        simp only [WeierstrassCurve.Affine.negY, MontgomeryCurveCurve25519, zero_mul, sub_zero,
          neg_neg, not_and]
        simp only [MontgomeryCurveCurve25519, ne_eq, some.injEq, not_and] at nonP
        exact nonP
      have h₂ : MontgomeryCurveCurve25519.Nonsingular x₂
          (MontgomeryCurveCurve25519.negY x₂ y₂) := by
        rw [WeierstrassCurve.Affine.nonsingular_neg]
        exact nonS₂
      have := @WeierstrassCurve.Affine.Point.add_some CurveField _ MontgomeryCurveCurve25519 _
          x₁ x₂ y₁ (MontgomeryCurveCurve25519.negY x₂ y₂) hxy_neg nonS₁ h₂
      simp only [WeierstrassCurve.Affine.negY, this, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, neg_add_rev]
      simp only [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY,
        MontgomeryCurveCurve25519, zero_mul, sub_zero, neg_neg, sub_neg_eq_add, ite_pow, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_ite, mul_zero, ite_self, add_zero]
      by_cases eq: x₁ = x₂
      · simp only [eq, ↓reduceIte, sub_self, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, mul_zero]
        simp only [eq, WeierstrassCurve.Affine.negY, MontgomeryCurveCurve25519, zero_mul,
          sub_zero, neg_neg, true_and] at hxy_neg
        simp only [eq, WeierstrassCurve.Affine.negY, MontgomeryCurveCurve25519, zero_mul,
          sub_zero, true_and] at hxy
        rw [nonsingular_iff, WeierstrassCurve.Affine.equation_iff,
          MontgomeryCurveCurve25519] at nonS₁
        simp only [eq, zero_mul, add_zero, one_mul] at nonS₁
        rw [nonsingular_iff, WeierstrassCurve.Affine.equation_iff,
          MontgomeryCurveCurve25519] at nonS₂
        simp only [zero_mul, add_zero, one_mul, ← nonS₁] at nonS₂
        have : (y₁ - y₂) * (y₁ + y₂) = 0 := by grind
        simp only [mul_eq_zero] at this
        have eq1 : ¬ y₁ - y₂ = 0 := by grind
        simp only [eq1, false_or] at this
        have eq1 : ¬ y₁ + y₂ = 0 := by grind
        simp [eq1] at this
      · simp only [eq, ↓reduceIte]
        have : (x₁ - x₂) ≠ 0 := by grind
        field_simp
        ring_nf
        rw [nonsingular_iff, WeierstrassCurve.Affine.equation_iff,
          MontgomeryCurveCurve25519] at nonS₁
        simp only [zero_mul, add_zero, one_mul] at nonS₁
        rw [nonsingular_iff, WeierstrassCurve.Affine.equation_iff,
          MontgomeryCurveCurve25519] at nonS₂
        simp only [zero_mul, add_zero, one_mul] at nonS₂
        have : y₁ ^ 4 = (y₁) ^ 2 * y₁ ^ 2 := by ring
        rw [this]
        have : y₂ ^ 4 = (y₂) ^ 2 * y₂ ^ 2 := by ring
        rw [this]
        simp only [nonS₁, nonS₂]
        ring_nf

lemma non_IsQuase : ¬ IsSquare ((Curve25519.A^2 -4)) := by
  unfold Curve25519.A
  ring_nf
  apply(@legendreSym.eq_neg_one_iff' p _ (236839902240)).mp
  norm_num [p]

lemma A_minus_two_non_square : ¬ IsSquare (Curve25519.A - 2) := by
  unfold Curve25519.A
  ring_nf
  apply(@legendreSym.eq_neg_one_iff' p _ (486660)).mp
  norm_num [p]

lemma A_plus_two_square : IsSquare (Curve25519.A + 2) := by
  unfold Curve25519.A
  ring_nf
  apply ((@legendreSym.eq_one_iff p _ (486664)) (by grind)).mp
  norm_num [p]

lemma quadratic_ne_zero (x : CurveField) : ¬ x ^ 2 + Curve25519.A * x + 1 = 0 := by
  intro h
  have : x ^ 2 + Curve25519.A * x + 1 =
      (x + Curve25519.A / 2)^2 + 1 - Curve25519.A^2 / 4 := by grind
  rw [this] at h
  have : (2 * (x + Curve25519.A / 2)) ^ 2 = (Curve25519.A ^ 2 - 4) := by grind
  apply non_IsQuase
  unfold IsSquare
  use (2 * (x + Curve25519.A / 2))
  rw [← this]
  ring_nf

theorem DBL_neq_zero (P : Point) (PZero : P ≠ 0) (nPT : P ≠ T_point) :
    2 • P ≠ 0 := by
  intro h
  have hneg : P = -P := by grind
  · rcases P
    · simp [zero_def] at PZero
    · rename_i x y nonP
      simp only [MontgomeryCurveCurve25519, neg_some, WeierstrassCurve.Affine.negY, zero_mul,
        sub_zero, some.injEq, true_and] at hneg
      have eq : 2 * y = 0 := by grind
      simp only [mul_eq_zero] at eq
      have : (2:CurveField) ≠ 0 := by decide
      simp only [this, false_or] at eq
      simp only [WeierstrassCurve.Affine.Nonsingular, MontgomeryCurveCurve25519, eq,
        WeierstrassCurve.Affine.equation_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_mul, mul_zero, add_zero, one_mul] at nonP
      field_simp at nonP
      simp only [zero_eq_mul] at nonP
      have := quadratic_ne_zero x
      field_simp at this
      simp only [this, or_false] at nonP
      simp [T_point, eq, nonP.left] at nPT

theorem uDBL (P : Point) (PZero : P ≠ 0) (nPT : P ≠ T_point) :
    4 * get_u (2 • P) * get_u (P) * ((get_u P)^2 + Curve25519.A * get_u P + 1) =
    ((get_u P) ^ 2 - 1)^2 := by
  by_cases hneg : P = -P
  · rcases P
    · simp [zero_def] at PZero
    · rename_i x y nonP
      simp only [MontgomeryCurveCurve25519, neg_some, WeierstrassCurve.Affine.negY, zero_mul,
        sub_zero, some.injEq, true_and] at hneg
      have eq : 2 * y = 0 := by grind
      simp only [mul_eq_zero] at eq
      have : (2:CurveField) ≠ 0 := by decide
      simp only [this, false_or] at eq
      simp only [WeierstrassCurve.Affine.Nonsingular, MontgomeryCurveCurve25519, eq,
        WeierstrassCurve.Affine.equation_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_mul, mul_zero, add_zero, one_mul] at nonP
      field_simp at nonP
      simp only [zero_eq_mul] at nonP
      have := quadratic_ne_zero x
      field_simp at this
      simp only [this, or_false] at nonP
      simp [T_point, eq, nonP.left] at nPT
  · have : 2 • P = P + P := by grind
    rw [this]
    unfold get_u
    rcases P
    · simp only [zero_def, ne_eq, not_true_eq_false] at PZero
    · rename_i x y nonS
      have : y≠ MontgomeryCurveCurve25519.negY x y := by
        simp only [WeierstrassCurve.Affine.negY, MontgomeryCurveCurve25519, zero_mul, sub_zero,
          ne_eq]
        simp only [MontgomeryCurveCurve25519, neg_some, WeierstrassCurve.Affine.negY, zero_mul,
          sub_zero, some.injEq, true_and] at hneg
        exact hneg
      have := @WeierstrassCurve.Affine.Point.add_self_of_Y_ne' CurveField _ _ _ x y nonS this
      simp only [MontgomeryCurveCurve25519, neg_some, WeierstrassCurve.Affine.negY, zero_mul,
        sub_zero, some.injEq, true_and] at hneg
      simp only [MontgomeryCurveCurve25519, this, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.slope, ↓reduceIte, WeierstrassCurve.Affine.negY, zero_mul,
        sub_zero, hneg, sub_neg_eq_add, add_zero, WeierstrassCurve.Affine.negAddY,
        neg_some, neg_add_rev]
      simp only [MontgomeryCurveCurve25519, T_point, ne_eq, some.injEq, not_and] at nPT
      by_cases nony: y=0
      · simp only [nony, _root_.neg_zero, not_true_eq_false] at hneg
      · have : y + y = 2 * y := by ring_nf
        rw [this]
        field_simp
        simp only [WeierstrassCurve.Affine.Nonsingular,
          WeierstrassCurve.Affine.equation_iff, ne_eq] at nonS
        have := nonS.left
        simp only [MontgomeryCurveCurve25519, zero_mul, add_zero, one_mul] at this
        simp only [this]
        ring_nf

/-- Addition is associative for points.
This follows directly from mathlib's AddCommGroup instance for Weierstrass curve points. -/
theorem add_assoc' (P Q R : Point) : (P + Q) + R = P + (Q + R) :=
  add_assoc P Q R

theorem add_mk_point (m₁ m₂ : Point)
    (hsum : (m₁ + m₂) ≠ 0) :
    m₁ + m₂ = mk_point (point_on_curve (m₁ + m₂) hsum) := by
  apply mk_point_def
  apply hsum

@[simp]
lemma slope_of_Y_eq {x₁ x₂ y₁ y₂ : CurveField} (hx : x₁ = x₂) (hy : y₁ = -y₂) :
    MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂ = 0 := by
  apply WeierstrassCurve.Affine.slope_of_Y_eq
  all_goals simp_all [MontgomeryCurveCurve25519]

@[simp]
lemma slope_of_Y_ne' {x₂ y₁ y₂ : CurveField} (hy : ¬y₁ = -y₂) :
    MontgomeryCurveCurve25519.slope x₂ x₂ y₁ y₂ =
      (3 * x₂ ^ 2 + 2 * Curve25519.A * x₂ + 1) / (2 * y₁) := by
  simp only [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY,
    MontgomeryCurveCurve25519]
  grind [Curve25519.A]

@[simp]
lemma slope_of_Y_ne {x₁ x₂ y₁ y₂ : CurveField} (hx : x₁ = x₂) (hy : y₁ ≠ -y₂) :
    MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂ =
      (3 * x₁ ^ 2 + 2 * Curve25519.A * x₁ + 1) / (2 * y₁) := by
  simp_all only [MontgomeryCurveCurve25519, zero_mul, sub_zero, not_false_eq_true,
    WeierstrassCurve.Affine.slope_of_Y_ne']
  ring

@[simp]
lemma slope_of_X_ne {x₁ x₂ y₁ y₂ : CurveField} (hx : x₁ ≠ x₂) :
    MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := by
  rw [WeierstrassCurve.Affine.slope, if_neg hx]

lemma addX_eq_addX_negY_sub {x₁ x₂ : CurveField} (y₁ y₂ : CurveField) (hx : x₁ ≠ x₂) :
    MontgomeryCurveCurve25519.addX x₁ x₂ (MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂) =
      MontgomeryCurveCurve25519.addX x₁ x₂ (MontgomeryCurveCurve25519.slope x₁ x₂ y₁ <|
        MontgomeryCurveCurve25519.negY x₂ y₂) -
      (y₁ - MontgomeryCurveCurve25519.negY x₁ y₁) *
        (y₂ - MontgomeryCurveCurve25519.negY x₂ y₂) / (x₂ - x₁) ^ 2 := by
  simp_rw [slope_of_X_ne hx, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    ← neg_sub x₁, neg_sq]
  simp only [field]
  ring1

lemma addX_spec {x₁ x₂ : CurveField} (y₁ y₂ : CurveField) (hx : x₁ ≠ x₂) :
    MontgomeryCurveCurve25519.addX x₁ x₂ (MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂)
    = ((y₁ - y₂) / (x₁ - x₂) )^2 - Curve25519.A - x₁ - x₂ := by
  simp only [WeierstrassCurve.Affine.addX, MontgomeryCurveCurve25519, Curve25519.A, zero_mul,
    add_zero, sub_left_inj]
  rw [WeierstrassCurve.Affine.slope, if_neg hx]

end Montgomery
