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
open Edwards FieldElement51

/-- Convert a FieldElement51 to the mathematical field element in ZMod p.
    This is the same as `field_from_limbs` but with dot notation support. -/
def FieldElement51.toField (fe : FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

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
/-- Validity predicate for ProjectivePoint.
    A ProjectivePoint (X, Y, Z) represents the affine point (X/Z, Y/Z).
    For this to be on Ed25519, we need: a*(X/Z)² + (Y/Z)² = 1 + d*(X/Z)²*(Y/Z)²
    Clearing denominators: a*X²*Z² + Y²*Z² = Z⁴ + d*X²*Y² -/
structure ProjectivePoint.IsValid (pp : ProjectivePoint) : Prop where
  /-- X, Y, Z are all valid field elements, i.e., limbs of each are bounded by 2^52. -/
  X_valid : pp.X.IsValid
  Y_valid : pp.Y.IsValid
  Z_valid : pp.Z.IsValid
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : pp.Z.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve : let X := pp.X.toField; let Y := pp.Y.toField; let Z := pp.Z.toField
             Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

open curve25519_dalek.backend.serial.u64.field in
/-- Validity predicate for CompletedPoint.
    A CompletedPoint (X, Y, Z, T) represents the affine point (X/Z, Y/T).
    For this to be on Ed25519, we need: a*(X/Z)² + (Y/T)² = 1 + d*(X/Z)²*(Y/T)²
    Clearing denominators: a*X²*T² + Y²*Z² = Z²*T² + d*X²*Y² -/
structure CompletedPoint.IsValid (cp : CompletedPoint) : Prop where
  /-- X, Y, Z, T are all valid field elements, i.e., limbs of each are bounded by 2^52. -/
  X_valid : cp.X.IsValid
  Y_valid : cp.Y.IsValid
  Z_valid : cp.Z.IsValid
  T_valid : cp.T.IsValid
  /-- The Z and T coordinates are non-zero. -/
  Z_ne_zero : cp.Z.toField ≠ 0
  T_ne_zero : cp.T.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve : let X := cp.X.toField; let Y := cp.Y.toField
             let Z := cp.Z.toField; let T := cp.T.toField
             Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2

/-- Convert a valid ProjectivePoint to the affine point (X/Z, Y/Z). -/
noncomputable def ProjectivePoint.toPoint (pp : ProjectivePoint) (h : pp.IsValid := by assumption) : Point Ed25519 :=
  let X := pp.X.toField
  let Y := pp.Y.toField
  let Z := pp.Z.toField
  { x := X / Z
    y := Y / Z
    on_curve := by
      -- Need to show: a*(X/Z)² + (Y/Z)² = 1 + d*(X/Z)²*(Y/Z)²
      -- From h.on_curve: a*X²*Z² + Y²*Z² = Z⁴ + d*X²*Y²
      -- Divide both sides by Z⁴
      have hz : Z ≠ 0 := h.Z_ne_zero
      have hz2 : Z^2 ≠ 0 := pow_ne_zero 2 hz
      have hz4 : Z^4 ≠ 0 := pow_ne_zero 4 hz
      have hcurve : Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2 := h.on_curve
      simp only [Ed25519] at hcurve ⊢
      simp only [div_pow]
      field_simp [hz2, hz4]
      linear_combination hcurve }

/-- Convert a valid CompletedPoint to the affine point (X/Z, Y/T). -/
noncomputable def CompletedPoint.toPoint (cp : CompletedPoint) (h : cp.IsValid := by assumption) : Point Ed25519 :=
  let X := cp.X.toField
  let Y := cp.Y.toField
  let Z := cp.Z.toField
  let T := cp.T.toField
  { x := X / Z
    y := Y / T
    on_curve := by
      -- Need to show: a*(X/Z)² + (Y/T)² = 1 + d*(X/Z)²*(Y/T)²
      -- From h.on_curve: a*X²*T² + Y²*Z² = Z²*T² + d*X²*Y²
      -- Divide both sides by Z²*T²
      have hz : Z ≠ 0 := h.Z_ne_zero
      have ht : T ≠ 0 := h.T_ne_zero
      have hz2 : Z^2 ≠ 0 := pow_ne_zero 2 hz
      have ht2 : T^2 ≠ 0 := pow_ne_zero 2 ht
      have hcurve : Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2 := h.on_curve
      simp only [Ed25519] at hcurve ⊢
      simp only [div_pow]
      field_simp [hz2, ht2]
      linear_combination hcurve }

/-- Total conversion function for ProjectivePoint.
    If valid, returns the point (X/Z, Y/Z). If invalid, returns 0. -/
noncomputable def ProjectivePoint.toPoint' (pp : ProjectivePoint) : Point Ed25519 := by
  classical
  exact if h : pp.IsValid then pp.toPoint h else 0

/-- Total conversion function for CompletedPoint.
    If valid, returns the point (X/Z, Y/T). If invalid, returns 0. -/
noncomputable def CompletedPoint.toPoint' (cp : CompletedPoint) : Point Ed25519 := by
  classical
  exact if h : cp.IsValid then cp.toPoint h else 0

/-- If a ProjectivePoint is valid, `toPoint'` equals `toPoint`. -/
theorem ProjectivePoint.toPoint'_eq_toPoint {pp : ProjectivePoint} (h : pp.IsValid) :
    pp.toPoint' = pp.toPoint h := by
  rw [toPoint', dif_pos h]

/-- If a CompletedPoint is valid, `toPoint'` equals `toPoint`. -/
theorem CompletedPoint.toPoint'_eq_toPoint {cp : CompletedPoint} (h : cp.IsValid) :
    cp.toPoint' = cp.toPoint h := by
  rw [toPoint', dif_pos h]

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
