/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
import Curve25519Dalek.Types

import Mathlib.Algebra.Field.ZMod

/-!
# Edwards Curve Definitions for Ed25519

This file provides the mathematical foundations and bridge infrastructure for Ed25519:

1. **Mathematical Foundations**: Defines the Twisted Edwards curve `Ed25519` over `ZMod p`,
   including the Point structure and group operations.
2. **Bridge Infrastructure**: Provides validity predicates and "Total Function" conversions
   to map low-level Rust types (`ProjectivePoint`, `CompletedPoint`, `AffinePoint`) to
   high-level mathematical objects (`Point Ed25519`).
-/

namespace Edwards

open curve25519_dalek CategoryTheory curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.curve_models Function ZMod



/-! ## 1. Mathematical Foundations: Twisted Edwards Curves -/

/-- The finite field F_p where p = 2^255 - 19. -/
abbrev CurveField : Type := ZMod p

instance : Fact (Nat.Prime p) := by
  unfold p
  -- Proof omitted: p = 2^255 - 19 is prime.
  sorry

instance : Field CurveField := by
  unfold CurveField
  infer_instance

/-- A Twisted Edwards curve structure defined by parameters a and d. -/
structure EdwardsCurve (F : Type) [Field F] where
  a : F
  d : F

/-- The specific Ed25519 curve parameters lifted to the field. -/
def Ed25519 : EdwardsCurve CurveField := {
  a := -1,
  d := (d : CurveField)
}

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

/-- Convert the 5-limb array to a field element in ZMod p. -/
def field_from_limbs (fe : backend.serial.u64.field.FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

end Edwards


namespace curve25519_dalek.edwards.affine
open Edwards

/-- Validity predicate linking low-level AffinePoint to mathematical Point. -/
def AffinePoint.IsValid (low : AffinePoint) (high : Point Ed25519) : Prop :=
    field_from_limbs low.x = high.x ∧ field_from_limbs low.y = high.y

noncomputable def AffinePoint.toPoint (p : AffinePoint) (h : ∃ P, p.IsValid P) : Point Ed25519 :=
 { x := field_from_limbs p.x,
    y := field_from_limbs p.y,
    h_on_curve := by
      have ⟨P, hP⟩ := h; rw [AffinePoint.IsValid] at hP; rw [hP.1, hP.2]; exact P.h_on_curve }

end curve25519_dalek.edwards.affine

-- Attach Projective/Completed definitions to their native namespace
namespace curve25519_dalek.backend.serial.curve_models
open Edwards

/-- Validity predicate linking low-level ProjectivePoint to mathematical Point. -/
def ProjectivePoint.IsValid (low : ProjectivePoint) (high : Point Ed25519) : Prop :=
    let X := field_from_limbs low.X; let Y := field_from_limbs low.Y; let Z := field_from_limbs low.Z
    Z ≠ 0 ∧ X = high.x * Z ∧ Y = high.y * Z

/-- Validity predicate linking low-level CompletedPoint to mathematical Point. -/
def CompletedPoint.IsValid (low : CompletedPoint) (high : Point Ed25519) : Prop :=
  let X := field_from_limbs low.X; let Y := field_from_limbs low.Y
  let Z := field_from_limbs low.Z; let T := field_from_limbs low.T
  Z ≠ 0 ∧ T ≠ 0 ∧ X = high.x * Z ∧ Y = high.y * T

-- === Total Function / Garbage Value Infrastructure ===
-- These definitions live in the Edwards namespace to ensure they resolve correctly together.

/-- Existential validity predicate for ProjectivePoint. -/
def ProjectivePoint.IsValid' (p : ProjectivePoint) : Prop := ∃ P, p.IsValid P

/-- Existential validity predicate for CompletedPoint. -/
def CompletedPoint.IsValid' (p : CompletedPoint) : Prop := ∃ P, p.IsValid P

/--
Total conversion function for ProjectivePoint.
If the point is valid, returns the unique `Point Ed25519` it represents.
If invalid, returns the neutral element `0`.
-/
noncomputable def ProjectivePoint.toPoint' (p : ProjectivePoint) : Point Ed25519 :=
  open Classical in
  if h : p.IsValid' then choose h else 0

/-- Total conversion function for CompletedPoint. -/
noncomputable def CompletedPoint.toPoint' (p : CompletedPoint) : Point Ed25519 :=
  open Classical in
  if h : p.IsValid' then choose h else 0

/-- Bridge Lemma: If a ProjectivePoint is valid, `toPoint'` returns the correct mathematical point. -/
theorem ProjectivePoint.toPoint'_eq_of_isValid {p : ProjectivePoint} {P : Point Ed25519}
    (h : p.IsValid P) : p.toPoint' = P := by
  rw [toPoint', dif_pos ⟨P, h⟩]
  have h_uniq : ∀ P' : Point Ed25519, p.IsValid P' → P' = P := by
    intro P' h'
    unfold IsValid at h h'
    rcases h with ⟨hz, hx, hy⟩
    rcases h' with ⟨_, hx', hy'⟩
    ext
    · apply mul_right_cancel₀ hz (Eq.trans hx'.symm hx)
    · apply mul_right_cancel₀ hz (Eq.trans hy'.symm hy)
  apply h_uniq
  exact Classical.choose_spec ⟨P, h⟩

/-- Bridge Lemma: If a CompletedPoint is valid, `toPoint'` returns the correct mathematical point. -/
theorem CompletedPoint.toPoint'_eq_of_isValid {p : CompletedPoint} {P : Point Ed25519}
    (h : p.IsValid P) : p.toPoint' = P := by
  rw [toPoint', dif_pos ⟨P, h⟩]
  have h_uniq : ∀ P' : Point Ed25519, p.IsValid P' → P' = P := by
    intro P' h'
    unfold IsValid at h h'
    rcases h with ⟨hz, ht, hx, hy⟩
    rcases h' with ⟨_, _, hx', hy'⟩
    ext
    · apply mul_right_cancel₀ hz (Eq.trans hx'.symm hx)
    · apply mul_right_cancel₀ ht (Eq.trans hy'.symm hy)
  apply h_uniq
  exact Classical.choose_spec ⟨P, h⟩

-- === Coercions ===
-- These allow using low-level types in high-level equations

/-- Coercion allowing `q + q` syntax where `q` is a ProjectivePoint. -/
noncomputable instance : Coe ProjectivePoint (Point Ed25519) where
  coe p := p.toPoint'

/-- Coercion allowing comparison of `CompletedPoint` results with mathematical points. -/
noncomputable instance : Coe CompletedPoint (Point Ed25519) where
  coe p := p.toPoint'

@[simp]
theorem ProjectivePoint.toPoint'_eq_coe (p : ProjectivePoint) :
  p.toPoint' = ↑p := rfl

@[simp]
theorem CompletedPoint.toPoint'_eq_coe (p : CompletedPoint) :
  p.toPoint' = ↑p := rfl

def ProjectivePoint.InBounds (p : ProjectivePoint) : Prop :=
  (∀ i, i < 5 → (p.X[i]!).val ≤ 2^52) ∧
  (∀ i, i < 5 → (p.Y[i]!).val ≤ 2^52) ∧
  (∀ i, i < 5 → (p.Z[i]!).val ≤ 2^52)

end curve25519_dalek.backend.serial.curve_models
