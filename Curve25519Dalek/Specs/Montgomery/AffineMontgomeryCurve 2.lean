/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Defs

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.LinearCombination
import PrimeCert.PrimeList

/-!
# Affine Montgomery Curve Points for Curve25519

This file defines affine point arithmetic on Montgomery curves,
focusing on the affine coordinate representation (u, v).

## Contents

1. **Field Definitions**: `CurveField` as `ZMod p` where p = 2^255 - 19
2. **Curve Structure**: Generic `MontgomeryCurve` and the specific `Curve25519` instance
3. **Affine Point Structure**: Points (u, v) satisfying B·v² = u³ + A·u² + u
4. **Group Law**: Addition formulas and group structure for affine points

## Architecture Note

This file focuses on affine coordinate arithmetic for Montgomery curves.
For projective coordinates, see `ProjectiveMontgomeryCurve.lean`.

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

/-- Helper lemma for modular arithmetic lifting -/
theorem lift_mod_eq (a b : ℕ) (h : a % p = b % p) : (a : CurveField) = (b : CurveField) := by
  exact (ZMod.natCast_eq_natCast_iff a b p).mpr h

/-- A Montgomery curve structure defined by parameters A and B.
    The curve equation is: B·v² = u³ + A·u² + u -/
structure MontgomeryCurve (F : Type) [DecidableEq F] [Zero F] where
  A : F
  B : F
  B_Ne_Zero : ¬ B = 0

/-- The specific Curve25519 Montgomery curve parameters.
    * A = 486662
    * B = 1
    The curve equation is: v² = u³ + 486662·u² + u -/
def Curve25519 : MontgomeryCurve CurveField := {
  A := (486662 : CurveField),
  B := 1
  B_Ne_Zero := by simp
}





theorem Curve25519.A_eq : Curve25519.A = 486662 := rfl

theorem Curve25519.B_eq : Curve25519.B = 1 := rfl

/-! ## Affine Point Structure -/

inductive Point {F : Type} [DecidableEq F] [Zero F] [Mul F] [Add F] [Pow F ℕ] (C : MontgomeryCurve F)
  | zero
  | some {u v : F} (on_curve : C.B * v^2 = u^3 + C.A * u^2 + u := by grind)

variable {F : Type} [DecidableEq F] [Zero F] [Mul F] [Add F] [Pow F ℕ] (C : MontgomeryCurve F)

/-! ## Curve25519 Affine Points -/

/-- Type alias for points on Curve25519. -/
def Curve25519Point := Point Curve25519

instance : Inhabited Curve25519Point := ⟨.zero⟩

instance : Zero Curve25519Point := ⟨.zero⟩

lemma zero_def : (0 : Curve25519Point) = .zero := rfl

/-- The T point (0, 0) - a 2-torsion point. -/
def T_point : Curve25519Point := .some (u := 0) (v := 0)

/-- Create a point from coordinates with curve equation proof. -/
def mk_point (u v : CurveField)
    (h : Curve25519.B * v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u := by grind) :
    Curve25519Point :=
  .some (u := u) (v := v) (on_curve := h)

/-! ## Coordinate Extraction -/

/-- Extract u-coordinate from a point. -/
def get_u : Curve25519Point → CurveField
  | .zero => 0
  | .some (u := u) .. => u

/-- Extract v-coordinate from a point. -/
def get_v : Curve25519Point → CurveField
  | .zero => 0
  | .some (v := v) .. => v

@[simp] theorem get_u_zero : get_u (0: Curve25519Point) = 0 := rfl
@[simp] theorem get_v_zero : get_v (0: Curve25519Point) = 0 := rfl

@[simp] theorem get_u_T : get_u T_point = 0 := rfl
@[simp] theorem get_v_T : get_v T_point = 0 := rfl

/-! ## Group Law on Affine Points -/

variable {F : Type} [Field F] [DecidableEq F]

section GroupLaw

/-- Compute the slope λ for point addition when P ≠ Q.
    λ = (v_Q - v_P) / (u_Q - u_P) -/
def lambda_add (_C : MontgomeryCurve F) (u_P v_P u_Q v_Q : F) (_h : u_P ≠ u_Q) : F :=
  (v_Q - v_P) / (u_Q - u_P)

/-- Compute the slope λ for point doubling (when P = Q).
    λ = (3u_P² + 2Au_P + 1) / (2Bv_P) -/
def lambda_double (C : MontgomeryCurve F) (u_P v_P : F) (_h : C.B * v_P ≠ 0) : F :=
  (3 * u_P^2 + 2 * C.A * u_P + 1) / (2 * C.B * v_P)

/-- Compute the u-coordinate of P ⊕ Q given the slope λ.
    u_⊕ = B·λ² - (u_P + u_Q) - A -/
def u_sum (C : MontgomeryCurve F) (u_P u_Q lambda : F) (two_torsion_point : Bool) : F :=
  if two_torsion_point then 0 else C.B * lambda^2 - (u_P + u_Q) - C.A

/-- Compute the v-coordinate of P ⊕ Q given the slope λ and u_⊕.
    v_⊕ = λ·(u_P - u_⊕) - v_P -/
def v_sum (u_P v_P u_sum lambda : F) (two_torsion_point : Bool) : F :=
  if two_torsion_point then 0 else lambda * (u_P - u_sum) - v_P

/-- Addition formula for Montgomery curve points. -/
def add_coords [DecidableEq F] (C : MontgomeryCurve F) (p1 p2 : F × F) : F × F :=
by
  let (u_P, v_P) := p1
  let (u_Q, v_Q) := p2
  let same_point : Bool := u_P = u_Q
  let two_torsion_point : Bool := v_P = 0
  have h_denom :
      if same_point then
        (if two_torsion_point then v_P=0 else C.B * v_P ≠ 0)
        else (u_P ≠ u_Q) := by
    dsimp [same_point, two_torsion_point]
    simp[C.B_Ne_Zero]
  let lambda :=
    if h : same_point then
      (if h1 : two_torsion_point then 0 else
       (have h_double : C.B * v_P ≠ 0 := by
         split at h_denom <;> [exact h_denom; contradiction]
        lambda_double C u_P v_P h_double))
    else
      have h_add : u_P ≠ u_Q := by
        split at h_denom <;> [contradiction; exact h_denom]
      lambda_add C u_P v_P u_Q v_Q h_add
  let u_res := u_sum C u_P u_Q lambda two_torsion_point
  let v_res := v_sum u_P v_P u_res lambda two_torsion_point
  exact (u_res, v_res)

/-! ### Closure Properties -/

variable [DecidableEq F]

/-- Closure: The sum of two points stays on the curve. -/
theorem add_closure (C : MontgomeryCurve F)
    (P Q : Point C) :
    match P, Q with
    | .some (u := u_P) (v := v_P) .., .some (u := u_Q) (v := v_Q) .. =>
        let (u, v) := add_coords C (u_P, v_P) (u_Q, v_Q)
        C.B * v^2 = u^3 + C.A * u^2 + u
    | _, _ => True := by
    cases P <;> cases Q <;> simp <;> sorry

theorem add_coords_comm (C : MontgomeryCurve F) (u_P v_P u_Q v_Q : F) :
    add_coords C (u_P, v_P) (u_Q, v_Q) = add_coords C (u_Q, v_Q) (u_P, v_P) := by
  sorry

end GroupLaw

/-! ## Group Structure for Curve25519 Affine Points -/

section Curve25519Group

/-- Negation for points: (u, v) ↦ (u, -v). -/
def neg_point : Curve25519Point → Curve25519Point
  | .zero => .zero
  | .some (u := u) (v := v) (on_curve := h) =>
      .some (u := u) (v := -v) (on_curve := by
        simp only [neg_pow_two] at *
        exact h)

instance : Neg Curve25519Point := ⟨neg_point⟩

@[simp] theorem neg_identity : -(0: Curve25519Point) = (0: Curve25519Point) := rfl

@[simp] theorem neg_u_coord (P : Curve25519Point) :
    get_u (-P) = get_u P := by cases P <;> rfl

@[simp] theorem neg_v_coord (P : Curve25519Point) :
    get_v (-P) = -(get_v P) := by
  cases P
  · rfl
  · simp [get_v, Neg.neg, neg_point]

/-- Addition for points using the unified addition formula. -/
def add_point : Curve25519Point → Curve25519Point → Curve25519Point
  | .zero, Q => Q
  | P, .zero => P
  | .some (u := u_P) (v := v_P) (on_curve := h_P),
    .some (u := u_Q) (v := v_Q) (on_curve := h_Q) =>
    if u_P = u_Q ∧ v_P + v_Q = 0 then
    0
    else
      let coords := add_coords Curve25519 (u_P, v_P) (u_Q, v_Q)
      .some (u := coords.1) (v := coords.2) (on_curve := by
        have h_closure := add_closure Curve25519
            (.some (u := u_P) (v := v_P) (on_curve := h_P))
            (.some (u := u_Q) (v := v_Q) (on_curve := h_Q))
        simp at h_closure
        exact h_closure)

instance : Add Curve25519Point := ⟨add_point⟩

theorem zero_add (P : Curve25519Point) : (0: Curve25519Point) + P = P := by
  cases P <;> rfl

theorem add_zero (P : Curve25519Point) : P + (0: Curve25519Point) = P := by
  cases P <;> rfl

instance : Sub Curve25519Point where
  sub P Q := P + (-Q)

/-- Scalar multiplication by natural numbers. -/
def nsmul (n : ℕ) (P : Curve25519Point) : Curve25519Point :=
  match n with
  | 0 => (0: Curve25519Point)
  | n + 1 => P + (nsmul n P)

/-- Scalar multiplication by integers. -/
def zsmul (z : ℤ) (P : Curve25519Point) : Curve25519Point :=
  match z with
  | (n : ℕ) => nsmul n P
  | (Int.negSucc n) => -(nsmul (n + 1) P)

instance : SMul ℕ Curve25519Point := ⟨nsmul⟩
instance : SMul ℤ Curve25519Point := ⟨zsmul⟩

/-! ### Group Law Properties -/

/-- Addition is commutative for points. -/
theorem add_comm (P Q : Curve25519Point) : P + Q = Q + P := by
  cases P <;> cases Q
  · rfl
  · rfl
  · rfl
  · rename_i u_P v_P h_P u_Q v_Q h_Q
    simp only [HAdd.hAdd, Add.add, add_point]
    have h := add_coords_comm Curve25519 u_P v_P u_Q v_Q
    have h_symm : (u_P = u_Q ∧ v_P + v_Q = 0) ↔ (u_Q = u_P ∧ v_Q + v_P = 0) := by
      constructor
      · intro ⟨h1, h2⟩
        constructor
        · exact h1.symm
        · calc v_Q + v_P = v_P + v_Q := by ring
            _ = 0 := h2
      · intro ⟨h1, h2⟩
        constructor
        · exact h1.symm
        · calc v_P + v_Q = v_Q + v_P := by ring
            _ = 0 := h2
    by_cases hc : u_P = u_Q ∧ v_P + v_Q = 0
    · have hc2 := h_symm.mp hc
      change (if u_P = u_Q ∧ v_P + v_Q = 0 then 0 else _)  = (if u_Q = u_P ∧ v_Q + v_P = 0 then 0 else _)
      rw [if_pos hc, if_pos hc2]
    · have hc2 : ¬(u_Q = u_P ∧ v_Q + v_P = 0) := mt h_symm.mpr hc
      change (if u_P = u_Q ∧ v_P + v_Q = 0 then 0 else _) = (if u_Q = u_P ∧ v_Q + v_P = 0 then 0 else _)
      rw [if_neg hc, if_neg hc2]
      congr 1
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h

/-- Negation is a left inverse: -P + P = (0: Curve25519Point). -/
theorem neg_add_cancel (P : Curve25519Point) : -P + P = (0: Curve25519Point) := by
  cases P
  · rfl
  · rename_i u v h
    simp only [HAdd.hAdd, Add.add, add_point, Neg.neg, neg_point]
    have h_cond : True ∧ -v + v = 0 := by grind
    change (if True ∧ -v + v = 0 then 0 else _)  = 0
    rw [if_pos h_cond]

/-- Addition is associative: (P + Q) + R = P + (Q + R). -/
theorem add_assoc (P Q R : Curve25519Point) :
    P + Q + R = P + (Q + R) := by
  sorry

/-- nsmul satisfies the zero property. -/
theorem nsmul_zero (P : Curve25519Point) : nsmul 0 P = (0: Curve25519Point) := rfl

/-- nsmul satisfies the successor property. -/
theorem nsmul_succ (n : ℕ) (P : Curve25519Point) :
    nsmul (n + 1) P = nsmul n P + P := by
  rw [add_comm]; rfl

/-- zsmul satisfies the zero property. -/
theorem zsmul_zero (P : Curve25519Point) : zsmul 0 P = (0: Curve25519Point) := rfl

/-- zsmul satisfies the successor property. -/
theorem zsmul_succ (n : ℕ) (P : Curve25519Point) :
    zsmul (Int.ofNat n.succ) P = zsmul (Int.ofNat n) P + P := by
  simp only [zsmul]
  induction n with
  | zero =>
    simp only [nsmul]
    rw [add_zero, zero_add]
  | succ k _ih =>
    simp only [nsmul]
    rw [add_comm]

/-- The Curve25519 points form an additive abelian group. -/
instance : AddCommGroup Curve25519Point where
  add := Add.add
  add_assoc := add_assoc
  zero := (0: Curve25519Point)
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmul
  nsmul_zero := nsmul_zero
  neg := Neg.neg
  zsmul := zsmul
  zsmul_zero' := zsmul_zero
  neg_add_cancel := neg_add_cancel
  add_comm := add_comm
  nsmul_succ := nsmul_succ
  zsmul_succ' := zsmul_succ

end Curve25519Group





end Montgomery
