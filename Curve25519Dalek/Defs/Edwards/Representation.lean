/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
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

## Validity Predicates

The Rust code uses 9 different Rust structures for representing points on the elliptic curve:

- backend.serial.curve_models.ProjectivePoint
- backend.serial.curve_models.CompletedPoint
- backend.serial.curve_models.ProjectiveNielsPoint
- edwards.EdwardsPoint
- edwards.affine.AffinePoint
- edwards.CompressedEdwardsY
- montgomery.MontgomeryPoint
- ristretto.RistrettoPoint
- ristretto.CompressedRistretto

The Rust code is designed so that the constructors and the various operations guarantee that the
data held by any of these is always a valid combination of coordinates. To track this we introduce
Lean predicates for each of these represenations.
-/

namespace Edwards

open curve25519_dalek CategoryTheory curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.curve_models Function ZMod

/-- Convert the 5-limb array to a field element in ZMod p. -/
def field_from_limbs (fe : backend.serial.u64.field.FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

end Edwards

namespace curve25519_dalek.backend.serial.u64.field

/-- A FieldElement51 is valid when all 5 limbs are bounded by 2^52. -/
def FieldElement51.IsValid (fe : FieldElement51) : Prop :=
  ∀ i < 5, fe[i]!.val ≤ 2^52

end curve25519_dalek.backend.serial.u64.field


namespace curve25519_dalek.edwards.affine
open Edwards

/-- Validity predicate linking low-level AffinePoint to mathematical Point. -/
def AffinePoint.IsValid (low : AffinePoint) (high : Point Ed25519) : Prop :=
    field_from_limbs low.x = high.x ∧ field_from_limbs low.y = high.y

noncomputable def AffinePoint.toPoint (p : AffinePoint) (h : ∃ P, p.IsValid P) : Point Ed25519 :=
 { x := field_from_limbs p.x,
    y := field_from_limbs p.y,
    on_curve := by
      have ⟨P, hP⟩ := h; rw [AffinePoint.IsValid] at hP; rw [hP.1, hP.2]; exact P.on_curve }

end curve25519_dalek.edwards.affine



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

def CompressedRistretto.IsValid (c : CompressedRistretto) : Prop :=
  U8x32_as_Nat c < p ∧
  U8x32_as_Nat c % 2 = 0
  -- To do: this predicate is not complete yet, as some more complex
  -- properties also need to be checked for the field element corresponding to c
  -- to assure a valid compressed Ristretto point:
  -- (1) The square root computation in step_2 must succeed (invsqrt returns Choice.one)
  -- (2) The computed t coordinate must be non-negative (t.is_negative returns Choice.zero)
  -- (3) The computed y coordinate must be nonzero (y.is_zero returns Choice.zero)

end curve25519_dalek.ristretto




-- Attach Projective/Completed definitions to their native namespace
namespace curve25519_dalek.backend.serial.curve_models
open Edwards

open curve25519_dalek.backend.serial.u64.field in
/-- Relational validity predicate linking low-level ProjectivePoint to mathematical Point.
    Includes both the projective coordinate relations and limb bounds. -/
structure ProjectivePoint.IsValid' (low : ProjectivePoint) (high : Point Ed25519) : Prop where
  /-- All limbs of X are bounded by 2^52. -/
  X_bounds : FieldElement51.IsValid low.X
  /-- All limbs of Y are bounded by 2^52. -/
  Y_bounds : FieldElement51.IsValid low.Y
  /-- All limbs of Z are bounded by 2^52. -/
  Z_bounds : FieldElement51.IsValid low.Z
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : field_from_limbs low.Z ≠ 0
  /-- X represents high.x * Z. -/
  X_eq : field_from_limbs low.X = high.x * field_from_limbs low.Z
  /-- Y represents high.y * Z. -/
  Y_eq : field_from_limbs low.Y = high.y * field_from_limbs low.Z

open curve25519_dalek.backend.serial.u64.field in
/-- Validity predicate for CompletedPoint.
    A CompletedPoint (X, Y, Z, T) represents the affine point (X/Z, Y/T).
    For this to be on Ed25519, we need: a*(X/Z)² + (Y/T)² = 1 + d*(X/Z)²*(Y/T)²
    Clearing denominators: a*X²*T² + Y²*Z² = Z²*T² + d*X²*Y² -/
structure CompletedPoint.IsValid' (cp : CompletedPoint) : Prop where
  /-- X, Y, Z, T are all valid field elements, i.e., limbs of each are bounded by 2^52. -/
  X_bounds : FieldElement51.IsValid cp.X
  Y_bounds : FieldElement51.IsValid cp.Y
  Z_bounds : FieldElement51.IsValid cp.Z
  T_bounds : FieldElement51.IsValid cp.T
  /-- The Z and T coordinates are non-zero. -/
  Z_ne_zero : field_from_limbs cp.Z ≠ 0
  T_ne_zero : field_from_limbs cp.T ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve : let X := field_from_limbs cp.X; let Y := field_from_limbs cp.Y
             let Z := field_from_limbs cp.Z; let T := field_from_limbs cp.T
             Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2

/-- Existential validity predicate for ProjectivePoint. -/
def ProjectivePoint.IsValid (p : ProjectivePoint) : Prop :=
  ∃ P : Point Ed25519, p.IsValid' P

/-- Existential validity predicate for CompletedPoint. -/
def CompletedPoint.IsValid (p : CompletedPoint) : Prop :=
  ∃ P : Point Ed25519, p.IsValid' P

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
    ext
    · apply mul_right_cancel₀ h.Z_ne_zero (Eq.trans h'.X_eq.symm h.X_eq)
    · apply mul_right_cancel₀ h.Z_ne_zero (Eq.trans h'.Y_eq.symm h.Y_eq)
  apply h_uniq
  exact Classical.choose_spec ⟨P, h⟩

/-- Bridge Lemma: If a CompletedPoint is valid, `toPoint'` returns the correct mathematical point. -/
theorem CompletedPoint.toPoint'_eq_of_isValid {p : CompletedPoint} {P : Point Ed25519}
    (h : p.IsValid' P) : p.toPoint' = P := by
  rw [toPoint', dif_pos ⟨P, h⟩]
  have h_uniq : ∀ P' : Point Ed25519, p.IsValid' P' → P' = P := by
    intro P' h'
    ext
    · apply mul_right_cancel₀ h.Z_ne_zero (Eq.trans h'.X_eq.symm h.X_eq)
    · apply mul_right_cancel₀ h.T_ne_zero (Eq.trans h'.Y_eq.symm h.Y_eq)
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

open curve25519_dalek.backend.serial.u64.field in
/-- A ProjectivePoint has all coordinates in bounds. -/
def ProjectivePoint.InBounds (p : ProjectivePoint) : Prop :=
  FieldElement51.IsValid p.X ∧ FieldElement51.IsValid p.Y ∧ FieldElement51.IsValid p.Z

open curve25519_dalek.backend.serial.u64.field in
/-- A CompletedPoint has all coordinates in bounds. -/
def CompletedPoint.InBounds (p : CompletedPoint) : Prop :=
  FieldElement51.IsValid p.X ∧ FieldElement51.IsValid p.Y ∧
  FieldElement51.IsValid p.Z ∧ FieldElement51.IsValid p.T

end curve25519_dalek.backend.serial.curve_models
