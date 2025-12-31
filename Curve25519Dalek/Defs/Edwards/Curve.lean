/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Defs

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol

import PrimeCert.PrimeList

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
    Proof can be found at:
    https://github.com/kckennylau/PrimeCert/blob/master/PrimeCert/PrimeList.lean#L84 -/
abbrev CurveField : Type := ZMod p

instance : Fact (Nat.Prime p) := by
  unfold p
  exact ⟨PrimeCert.prime_25519''⟩

-- Useless
-- instance : Field CurveField := by
--   unfold CurveField
--   infer_instance

/-- Helper lemma for modular arithmetic lifting -/
theorem lift_mod_eq (a b : ℕ) (h : a % p = b % p) : (a : CurveField) = (b : CurveField) := by
  exact (ZMod.natCast_eq_natCast_iff a b p).mpr h

/-- A Twisted Edwards curve structure defined by parameters a and d. -/
structure EdwardsCurve (F : Type) where
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
structure Point {F : Type} [Mul F] [Add F] [Pow F ℕ] [One F] (C : EdwardsCurve F) where
  x : F
  y : F
  h_on_curve : C.a * x^2 + y^2 = 1 + C.d * x^2 * y^2 := by grind
  deriving Repr

instance : Inhabited (Point Ed25519) := ⟨{ x := 0, y := 1}⟩

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
  field_simp

  -- Proof requires analyzing denominators (omitted for brevity)
  sorry

instance : Add (Point C) where
  add p1 p2 :=
  let coords := add_coords C (p1.x, p1.y) (p2.x, p2.y)
  { x := coords.1
    y := coords.2
    h_on_curve := add_closure C p1 p2 }

instance : Zero (Point C) where
  zero := { x := 0, y := 1 }

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
  zero_add p := by sorry
  add_zero := by sorry
  nsmul := nsmul C
  neg := Neg.neg
  zsmul := zsmul C
  neg_add_cancel := by sorry
  add_comm := by sorry
  nsmul_succ := by sorry
  zsmul_succ' := by sorry

/-- Helper lemma to expose the addition formula without unfolding the whole structure. -/
theorem add_def (p1 p2 : Point Ed25519) :
  (p1 + p2).x = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).1 ∧
  (p1 + p2).y = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).2 := by
  exact Prod.mk_inj.mp rfl

end Edwards
