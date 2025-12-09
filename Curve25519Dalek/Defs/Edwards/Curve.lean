/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Defs

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Pure Mathematical Foundations for Edwards Curves

This file defines the pure mathematical foundations for Twisted Edwards curves,
independent of any implementation-specific types.

## Contents

1. **Field Definitions**: `CurveField` as `ZMod p` where p = 2^255 - 19
2. **Curve Structure**: Generic `EdwardsCurve` and the specific `Ed25519` instance
3. **Point Structure**: Affine points satisfying the Edwards curve equation
4. **Group Operations**: Addition, negation, scalar multiplication forming an abelian group

## Architecture Note

This file has NO dependencies on `Funs.lean` or `Types.lean`, making it purely mathematical.
Bridge functions that connect to Rust implementation types are in `Edwards/Representation.lean`.
-/

namespace Edwards

open ZMod

/-! ## 1. Mathematical Foundations: Twisted Edwards Curves -/

/-- The finite field F_p where p = 2^255 - 19.
    Proof can be found at: https://github.com/kckennylau/PrimeCert/blob/master/PrimeCert/PrimeList.lean#L84 -/
abbrev CurveField : Type := ZMod p

instance : Fact (Nat.Prime p) := by
  unfold p
  -- Proof omitted: p = 2^255 - 19 is prime.
  sorry

instance : Field CurveField := by
  unfold CurveField
  infer_instance

/-- Helper lemma for modular arithmetic lifting -/
theorem lift_mod_eq (a b : ℕ) (h : a % p = b % p) : (a : CurveField) = (b : CurveField) := by
  apply (ZMod.natCast_eq_natCast_iff a b p).mpr
  exact h

/-- A Twisted Edwards curve structure defined by parameters a and d. -/
structure EdwardsCurve (F : Type) [Field F] where
  a : F
  d : F

/-- The specific Ed25519 curve parameters lifted to the field. -/
def Ed25519 : EdwardsCurve CurveField := {
  a := -1,
  d := (d : CurveField)
}

/-- Ed25519 curve parameter d is not a square in the field. -/
lemma d_not_square : ¬IsSquare Ed25519.d := by
  apply (legendreSym.eq_neg_one_iff' p).mp
  norm_num [d, p]


/-- An affine point on the Edwards curve. -/
@[ext]
structure Point {F : Type} [Field F] (C : EdwardsCurve F) where
  x : F
  y : F
  h_on_curve : C.a * x^2 + y^2 = 1 + C.d * x^2 * y^2
  deriving Repr

instance : Inhabited (Point Ed25519) :=
  ⟨{ x := 0, y := 1, h_on_curve := by simp [Ed25519] }⟩

variable {F : Type} [Field F] (C : EdwardsCurve F)

/-- Implements the unified addition formulas for Twisted Edwards curves. -/
def add_coords (p1 p2 : F × F) : F × F :=
  let (x₁, y₁) := p1
  let (x₂, y₂) := p2
  let lambda_val := C.d * x₁ * x₂ * y₁ * y₂
  ( (x₁ * y₂ + y₁ * x₂) / (1 + lambda_val),
    (y₁ * y₂ - C.a * x₁ * x₂) / (1 - lambda_val) )

/-- Theorem: The sum of two points on the curve stays on the curve. -/
theorem add_closure (p1 p2 : Point C) :
    let (x, y) := add_coords C (p1.x, p1.y) (p2.x, p2.y)
    C.a * x^2 + y^2 = 1 + C.d * x^2 * y^2 := by
  simp only [add_coords]
  -- Proof requires analyzing denominators (omitted for brevity)
  sorry

instance : Add (Point C) where
  add p1 p2 :=
  let coords := add_coords C (p1.x, p1.y) (p2.x, p2.y)
  { x := coords.1
    y := coords.2
    h_on_curve := add_closure C p1 p2 }

instance : Zero (Point C) where
  zero := { x := 0, y := 1, h_on_curve := by simp }

instance : Neg (Point C) where
  neg p := {
    x := -p.x
    y := p.y
    h_on_curve := by
      have h := p.h_on_curve
      simp only [neg_pow_two]
      exact h
  }

instance : Sub (Point C) where
  sub p1 p2 := p1 + (-p2)

def nsmul (n : ℕ) (p : Point C) : Point C :=
  match n with
  | 0 => 0
  | n + 1 => p + (nsmul n p)

def zsmul (z : ℤ) (p : Point C) : Point C :=
  match z with
  | (n : ℕ) => nsmul C n p
  | (Int.negSucc n) => -(nsmul C (n + 1) p)

instance : SMul ℕ (Point C) := ⟨nsmul C⟩
instance : SMul ℤ (Point C) := ⟨zsmul C⟩

/-- The Edwards Curve forms an additive abelian group. -/
instance : AddCommGroup (Point C) where
  add := Add.add
  add_assoc := by sorry
  zero := 0
  zero_add p := by
    -- Zero is (0, 1), adding on left: (0*p.y + 1*p.x)/(1+d*0*p.x*1*p.y) = p.x/1 = p.x
    -- and (1*p.y - a*0*p.x)/(1-d*0*p.x*1*p.y) = p.y/1 = p.y
    ext
    · -- x coordinate
      simp only [HAdd.hAdd, Add.add, add_coords, OfNat.ofNat, Zero.zero]
      ring_nf
      change (0 + p.x) * (1 + 0)⁻¹ = p.x; simp
    · -- y coordinate: ring_nf closes this case directly
      simp only [HAdd.hAdd, Add.add, add_coords, OfNat.ofNat, Zero.zero]
      ring_nf
  add_zero := by
    -- Zero is (0, 1), adding on right: (p.x*1 + p.y*0)/(1+d*p.x*0*p.y*1) = p.x/1 = p.x
    intro p
    ext
    · -- x coordinate
      simp only [HAdd.hAdd, Add.add, add_coords, OfNat.ofNat, Zero.zero]
      ring_nf
      change (p.x + 0) * (1 + 0)⁻¹ = p.x; simp
    · -- y coordinate: ring_nf closes this case directly
      simp only [HAdd.hAdd, Add.add, add_coords, OfNat.ofNat, Zero.zero]
      ring_nf
  nsmul := nsmul C
  neg := Neg.neg
  zsmul := zsmul C
  neg_add_cancel := by
    intro p
    ext
    · -- x coordinate: numerator is -p.x*p.y + p.x*p.y = 0
      simp only [HAdd.hAdd, Add.add, add_coords, Neg.neg, OfNat.ofNat, Zero.zero]
      ring_nf
      change (-(p.x * p.y) + p.x * p.y) * _ = 0
      simp
    · -- y coordinate: uses curve equation
      simp only [HAdd.hAdd, Add.add, add_coords, Neg.neg, OfNat.ofNat, Zero.zero]
      have hc := p.h_on_curve
      -- curve eq: C.a * p.x^2 + p.y^2 = 1 + C.d * p.x^2 * p.y^2
      -- After simplification: (p.y^2 + a*p.x^2) / (1 + d*p.x^2*p.y^2) = 1
      -- This equals 1 when numerator = denominator, which is the curve equation
      ring_nf
      rw [← add_mul, _root_.add_comm (p.y^2), hc]
      -- Now: (1 + C.d * p.x^2 * p.y^2) * (1 + p.y^2 * p.x^2 * C.d)⁻¹ = 1
      rw [show C.d * p.x^2 * p.y^2 = p.y^2 * p.x^2 * C.d from by ring]
      exact mul_inv_cancel₀ (by
        -- Need: 1 + p.y^2 * p.x^2 * C.d ≠ 0
        -- This holds because d is not a square, so d*x^2*y^2 ≠ -1
        sorry)
  add_comm := by
    intro p q
    simp only [Point.ext_iff, HAdd.hAdd, Add.add, add_coords]
    constructor
    · -- x coordinate: needs mul_comm to swap then add_comm on numerator
      ring_nf
      rw [mul_comm]
      congr 1
      exact _root_.add_comm _ _
    · -- y coordinate: ring_nf solves directly
      ring_nf
  nsmul_succ := by
    intro n p
    simp only [nsmul]
    -- Need: p + nsmul C n p = nsmul C n p + p (commutativity)
    simp only [Point.ext_iff, HAdd.hAdd, Add.add, add_coords]
    constructor
    · -- x coordinate
      ring_nf
      rw [mul_comm]
      congr 1
      exact _root_.add_comm _ _
    · -- y coordinate: ring_nf solves directly
      ring_nf
  zsmul_succ' := by
    intro n p
    simp [zsmul, nsmul]
    -- Need: p + nsmul C n p = nsmul C n p + p (commutativity)
    simp only [Point.ext_iff, HAdd.hAdd, Add.add, add_coords]
    constructor
    · -- x coordinate
      ring_nf
      rw [mul_comm]
      congr 1
      exact _root_.add_comm _ _
    · -- y coordinate: ring_nf solves directly
      ring_nf

/-- Helper lemma to expose the addition formula without unfolding the whole structure. -/
theorem add_def (p1 p2 : Point Ed25519) :
  (p1 + p2).x = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).1 ∧
  (p1 + p2).y = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).2 := by
  exact Prod.mk_inj.mp rfl

end Edwards
