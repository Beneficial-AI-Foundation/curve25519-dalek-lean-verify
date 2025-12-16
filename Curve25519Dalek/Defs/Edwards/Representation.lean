/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Markus Dablander
-/
import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
import Curve25519Dalek.Types
import Curve25519Dalek.Defs.Edwards.Curve

import Mathlib.Algebra.Field.ZMod

/-!
# Bridge Infrastructure for Edwards Curve Representations

This file provides the bridge between low-level Rust implementation types
(ProjectivePoint, CompletedPoint, AffinePoint) and high-level mathematical
objects (Point Ed25519).

## Contents

1. **field_from_limbs**: Converts 5-limb FieldElement51 arrays to CurveField
2. **IsValid Predicates**: Link low-level representations to mathematical points
3. **Total Conversion Functions**: toPoint' with Classical choice for invalid inputs
4. **Coercions**: Enable natural syntax like `↑q` for conversions
5. **InBounds**: Hardware bounds checking predicates

## Architecture Note

This file imports `Funs.lean` and `Types.lean` to access Rust implementation types.
It also imports `Edwards.EdCurve` to access the pure mathematical definitions.
-/

namespace Edwards

open curve25519_dalek CategoryTheory curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.curve_models Function ZMod

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


-- === Validity Predicates ===

namespace curve25519_dalek.edwards

def EdwardsPoint.IsValid (e : EdwardsPoint) : Prop :=
  let X := Field51_as_Nat e.X
  let Y := Field51_as_Nat e.Y
  let Z := Field51_as_Nat e.Z
  let T := Field51_as_Nat e.T
  ¬(Z ≡ 0 [MOD p]) ∧
  X * Y ≡ T * Z [MOD p] ∧
  Y ^ 2 ≡ X ^ 2 + Z ^ 2 + d * T ^ 2 [MOD p]

end curve25519_dalek.edwards

namespace curve25519_dalek.ristretto
open curve25519_dalek.edwards

def RistrettoPoint.IsValid (r : RistrettoPoint) : Prop :=
  EdwardsPoint.IsValid r
-- To do: potentially add extra information regarding canonical representation of Ristretto point

end curve25519_dalek.ristretto

namespace curve25519_dalek.backend.serial.curve_models
open Edwards

/-- Existential validity predicate for ProjectivePoint. -/
def ProjectivePoint.IsValid (p : ProjectivePoint) : Prop :=
  ∃ P : Point Ed25519,
    let X := field_from_limbs p.X; let Y := field_from_limbs p.Y; let Z := field_from_limbs p.Z
    Z ≠ 0 ∧ X = P.x * Z ∧ Y = P.y * Z

/-- Existential validity predicate for CompletedPoint. -/
def CompletedPoint.IsValid (p : CompletedPoint) : Prop :=
  ∃ P : Point Ed25519,
    let X := field_from_limbs p.X; let Y := field_from_limbs p.Y
    let Z := field_from_limbs p.Z; let T := field_from_limbs p.T
    Z ≠ 0 ∧ T ≠ 0 ∧ X = P.x * Z ∧ Y = P.y * T

/-- Relational validity predicate linking low-level ProjectivePoint to mathematical Point. -/
def ProjectivePoint.IsValid' (low : ProjectivePoint) (high : Point Ed25519) : Prop :=
    let X := field_from_limbs low.X; let Y := field_from_limbs low.Y; let Z := field_from_limbs low.Z
    Z ≠ 0 ∧ X = high.x * Z ∧ Y = high.y * Z

/-- Relational validity predicate linking low-level CompletedPoint to mathematical Point. -/
def CompletedPoint.IsValid' (low : CompletedPoint) (high : Point Ed25519) : Prop :=
  let X := field_from_limbs low.X; let Y := field_from_limbs low.Y
  let Z := field_from_limbs low.Z; let T := field_from_limbs low.T
  Z ≠ 0 ∧ T ≠ 0 ∧ X = high.x * Z ∧ Y = high.y * T

/--
Total conversion function for ProjectivePoint.
If the point is valid, returns the unique `Point Ed25519` it represents.
If invalid, returns the neutral element `0`.
-/
noncomputable def ProjectivePoint.toPoint' (p : ProjectivePoint) : Point Ed25519 := by
  classical
  exact if h : p.IsValid then Classical.choose h else 0

/-- Total conversion function for CompletedPoint. -/
noncomputable def CompletedPoint.toPoint' (p : CompletedPoint) : Point Ed25519 := by
  classical
  exact if h : p.IsValid then Classical.choose h else 0

/-- Bridge Lemma: If a ProjectivePoint is valid, `toPoint'` returns the correct mathematical point. -/
theorem ProjectivePoint.toPoint'_eq_of_isValid {p : ProjectivePoint} {P : Point Ed25519}
    (h : p.IsValid' P) : p.toPoint' = P := by
  rw [toPoint', dif_pos ⟨P, h⟩]
  have h_uniq : ∀ P' : Point Ed25519, p.IsValid' P' → P' = P := by
    intro P' h'
    unfold IsValid' at h h'
    rcases h with ⟨hz, hx, hy⟩
    rcases h' with ⟨_, hx', hy'⟩
    ext
    · apply mul_right_cancel₀ hz (Eq.trans hx'.symm hx)
    · apply mul_right_cancel₀ hz (Eq.trans hy'.symm hy)
  apply h_uniq
  exact Classical.choose_spec ⟨P, h⟩

/-- Bridge Lemma: If a CompletedPoint is valid, `toPoint'` returns the correct mathematical point. -/
theorem CompletedPoint.toPoint'_eq_of_isValid {p : CompletedPoint} {P : Point Ed25519}
    (h : p.IsValid' P) : p.toPoint' = P := by
  rw [toPoint', dif_pos ⟨P, h⟩]
  have h_uniq : ∀ P' : Point Ed25519, p.IsValid' P' → P' = P := by
    intro P' h'
    unfold IsValid' at h h'
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
  (∀ i < 5, p.X[i]!.val ≤ 2^52) ∧
  (∀ i < 5, p.Y[i]!.val ≤ 2^52) ∧
  (∀ i < 5, p.Z[i]!.val ≤ 2^52)

end curve25519_dalek.backend.serial.curve_models
