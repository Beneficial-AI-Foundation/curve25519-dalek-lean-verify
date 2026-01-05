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

/-! ## FieldElement51 Validity

From the Rust source (field.rs):
> "In the 64-bit implementation, a `FieldElement` is represented in radix 2^51 as five u64s;
> the coefficients are allowed to grow up to 2^54 between reductions modulo p."

The bound `< 2^54` is the universal validity condition that:
- Is accepted as input by all field operations (mul, square, pow2k, sub)
- Encompasses all intermediate values between reductions
- Allows `as_projective` and `as_extended` conversions to work correctly
-/

/-- A FieldElement51 is valid when all 5 limbs are bounded by 2^54.
    This is the bound accepted as input by field operations and encompasses
    all valid intermediate values between reductions. -/
def FieldElement51.IsValid (fe : FieldElement51) : Prop :=
  ∀ i < 5, fe[i]!.val < 2^54

instance FieldElement51.instDecidableIsValid (fe : FieldElement51) : Decidable fe.IsValid :=
  show Decidable (∀ i < 5, fe[i]!.val < 2^54) from inferInstance

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
open curve25519_dalek.backend.serial.u64.field Edwards

def EdwardsPoint.IsValid (e : EdwardsPoint) : Prop :=
  let X := Field51_as_Nat e.X
  let Y := Field51_as_Nat e.Y
  let Z := Field51_as_Nat e.Z
  let T := Field51_as_Nat e.T
  ¬(Z ≡ 0 [MOD p]) ∧
  X * Y ≡ T * Z [MOD p] ∧
  Y ^ 2 ≡ X ^ 2 + Z ^ 2 + d * T ^ 2 [MOD p]

/-- Validity predicate for EdwardsPoint with bounds.
    An EdwardsPoint (X, Y, Z, T) represents the affine point (X/Z, Y/Z) with T = XY/Z.
    Bounds: all coordinates < 2^53 (needed for add operations where Y+X < 2^54). -/
structure EdwardsPoint.IsBounded (e : EdwardsPoint) : Prop where
  /-- X coordinate limbs are bounded by 2^53. -/
  X_bounds : ∀ i < 5, e.X[i]!.val < 2 ^ 53
  /-- Y coordinate limbs are bounded by 2^53. -/
  Y_bounds : ∀ i < 5, e.Y[i]!.val < 2 ^ 53
  /-- Z coordinate limbs are bounded by 2^53. -/
  Z_bounds : ∀ i < 5, e.Z[i]!.val < 2 ^ 53
  /-- T coordinate limbs are bounded by 2^53. -/
  T_bounds : ∀ i < 5, e.T[i]!.val < 2 ^ 53
  /-- The Z coordinate is non-zero in the field. -/
  Z_ne_zero : e.Z.toField ≠ 0
  /-- Extended coordinate relation: T = XY/Z, i.e., XY = TZ. -/
  T_relation : e.X.toField * e.Y.toField = e.T.toField * e.Z.toField
  /-- The curve equation (twisted Edwards). -/
  on_curve : let X := e.X.toField; let Y := e.Y.toField; let Z := e.Z.toField
             Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

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
    Clearing denominators: a*X²*Z² + Y²*Z² = Z⁴ + d*X²*Y²

    Note: ProjectivePoint coordinates must have the tighter bound < 2^52 (not just < 2^54)
    because operations like `double` compute X + Y, which must be < 2^54 for subsequent
    squaring. With coords < 2^52, we get X + Y < 2^53 < 2^54. -/
structure ProjectivePoint.IsValid (pp : ProjectivePoint) : Prop where
  /-- X coordinate limbs are bounded by 2^52 (needed for X + Y < 2^54 in double). -/
  X_bounds : ∀ i < 5, pp.X[i]!.val < 2 ^ 52
  /-- Y coordinate limbs are bounded by 2^52 (needed for X + Y < 2^54 in double). -/
  Y_bounds : ∀ i < 5, pp.Y[i]!.val < 2 ^ 52
  /-- Z coordinate limbs are bounded by 2^52. -/
  Z_bounds : ∀ i < 5, pp.Z[i]!.val < 2 ^ 52
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : pp.Z.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve : let X := pp.X.toField; let Y := pp.Y.toField; let Z := pp.Z.toField
             Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

open curve25519_dalek.backend.serial.u64.field in
/-- Validity predicate for CompletedPoint.
    A CompletedPoint (X, Y, Z, T) represents the affine point (X/Z, Y/T).
    For this to be on Ed25519, we need: a*(X/Z)² + (Y/T)² = 1 + d*(X/Z)²*(Y/T)²
    Clearing denominators: a*X²*T² + Y²*Z² = Z²*T² + d*X²*Y²

    All coordinates use the universal bound < 2^54, which:
    - Covers outputs from all operations (double, add) where bounds vary
    - Is sufficient for `as_projective` since mul accepts inputs < 2^54 -/
structure CompletedPoint.IsValid (cp : CompletedPoint) : Prop where
  /-- X coordinate is valid (limbs < 2^54). -/
  X_valid : cp.X.IsValid
  /-- Y coordinate is valid (limbs < 2^54). -/
  Y_valid : cp.Y.IsValid
  /-- Z coordinate is valid (limbs < 2^54). -/
  Z_valid : cp.Z.IsValid
  /-- T coordinate is valid (limbs < 2^54). -/
  T_valid : cp.T.IsValid
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : cp.Z.toField ≠ 0
  /-- The T coordinate is non-zero. -/
  T_ne_zero : cp.T.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve : let X := cp.X.toField; let Y := cp.Y.toField
             let Z := cp.Z.toField; let T := cp.T.toField
             Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2

open curve25519_dalek.backend.serial.u64.field in
/-- Validity predicate for ProjectiveNielsPoint.
    A ProjectiveNielsPoint (Y_plus_X, Y_minus_X, Z, T2d) represents precomputed values
    for mixed addition: Y+X, Y-X, Z, and 2dT where (X, Y, Z, T) is an EdwardsPoint.

    Bounds: all coordinates < 2^53 (needed for mixed addition operations). -/
structure ProjectiveNielsPoint.IsValid (pn : ProjectiveNielsPoint) : Prop where
  /-- Y_plus_X coordinate limbs are bounded by 2^53. -/
  Y_plus_X_bounds : ∀ i < 5, pn.Y_plus_X[i]!.val < 2 ^ 53
  /-- Y_minus_X coordinate limbs are bounded by 2^53. -/
  Y_minus_X_bounds : ∀ i < 5, pn.Y_minus_X[i]!.val < 2 ^ 53
  /-- Z coordinate limbs are bounded by 2^53. -/
  Z_bounds : ∀ i < 5, pn.Z[i]!.val < 2 ^ 53
  /-- T2d coordinate limbs are bounded by 2^53. -/
  T2d_bounds : ∀ i < 5, pn.T2d[i]!.val < 2 ^ 53

instance ProjectivePoint.instDecidableIsValid (pp : ProjectivePoint) : Decidable pp.IsValid :=
  if hX : ∀ i < 5, pp.X[i]!.val < 2 ^ 52 then
    if hY : ∀ i < 5, pp.Y[i]!.val < 2 ^ 52 then
      if hZ : ∀ i < 5, pp.Z[i]!.val < 2 ^ 52 then
        if hZne : pp.Z.toField ≠ 0 then
          if hcurve : Ed25519.a * pp.X.toField^2 * pp.Z.toField^2 + pp.Y.toField^2 * pp.Z.toField^2
                    = pp.Z.toField^4 + Ed25519.d * pp.X.toField^2 * pp.Y.toField^2 then
            isTrue ⟨hX, hY, hZ, hZne, hcurve⟩
          else isFalse fun h => hcurve h.on_curve
        else isFalse fun h => hZne h.Z_ne_zero
      else isFalse fun h => hZ h.Z_bounds
    else isFalse fun h => hY h.Y_bounds
  else isFalse fun h => hX h.X_bounds

open curve25519_dalek.backend.serial.u64.field in
instance CompletedPoint.instDecidableIsValid (cp : CompletedPoint) : Decidable cp.IsValid :=
  if hX : cp.X.IsValid then
    if hY : cp.Y.IsValid then
      if hZ : cp.Z.IsValid then
        if hT : cp.T.IsValid then
          if hZne : cp.Z.toField ≠ 0 then
            if hTne : cp.T.toField ≠ 0 then
              if hcurve : Ed25519.a * cp.X.toField^2 * cp.T.toField^2 + cp.Y.toField^2 * cp.Z.toField^2
                        = cp.Z.toField^2 * cp.T.toField^2 + Ed25519.d * cp.X.toField^2 * cp.Y.toField^2 then
                isTrue ⟨hX, hY, hZ, hT, hZne, hTne, hcurve⟩
              else isFalse fun h => hcurve h.on_curve
            else isFalse fun h => hTne h.T_ne_zero
          else isFalse fun h => hZne h.Z_ne_zero
        else isFalse fun h => hT h.T_valid
      else isFalse fun h => hZ h.Z_valid
    else isFalse fun h => hY h.Y_valid
  else isFalse fun h => hX h.X_valid

/-- Convert a ProjectivePoint to the affine point (X/Z, Y/Z).
    Returns 0 if the point is not valid. -/
noncomputable def ProjectivePoint.toPoint (pp : ProjectivePoint) : Point Ed25519 :=
  if h : pp.IsValid then
    let X := pp.X.toField
    let Y := pp.Y.toField
    let Z := pp.Z.toField
    { x := X / Z
      y := Y / Z
      on_curve := by
        have hz : Z ≠ 0 := h.Z_ne_zero
        have hz2 : Z^2 ≠ 0 := pow_ne_zero 2 hz
        have hz4 : Z^4 ≠ 0 := pow_ne_zero 4 hz
        have hcurve : Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2 := h.on_curve
        simp only [Ed25519] at hcurve ⊢
        simp only [div_pow]
        field_simp [hz2, hz4]
        linear_combination hcurve }
  else 0

/-- Convert a CompletedPoint to the affine point (X/Z, Y/T).
    Returns 0 if the point is not valid. -/
noncomputable def CompletedPoint.toPoint (cp : CompletedPoint) : Point Ed25519 :=
  if h : cp.IsValid then
    let X := cp.X.toField
    let Y := cp.Y.toField
    let Z := cp.Z.toField
    let T := cp.T.toField
    { x := X / Z
      y := Y / T
      on_curve := by
        have hz : Z ≠ 0 := h.Z_ne_zero
        have ht : T ≠ 0 := h.T_ne_zero
        have hz2 : Z^2 ≠ 0 := pow_ne_zero 2 hz
        have ht2 : T^2 ≠ 0 := pow_ne_zero 2 ht
        have hcurve : Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2 := h.on_curve
        simp only [Ed25519] at hcurve ⊢
        simp only [div_pow]
        field_simp [hz2, ht2]
        linear_combination hcurve }
  else 0

/-- Unfolding lemma: when a ProjectivePoint is valid, toPoint computes (X/Z, Y/Z). -/
theorem ProjectivePoint.toPoint_of_isValid {pp : ProjectivePoint} (h : pp.IsValid) :
    (pp.toPoint).x = pp.X.toField / pp.Z.toField ∧
    (pp.toPoint).y = pp.Y.toField / pp.Z.toField := by
  unfold toPoint; rw [dif_pos h]; constructor <;> rfl

/-- Unfolding lemma: when a CompletedPoint is valid, toPoint computes (X/Z, Y/T). -/
theorem CompletedPoint.toPoint_of_isValid {cp : CompletedPoint} (h : cp.IsValid) :
    (cp.toPoint).x = cp.X.toField / cp.Z.toField ∧
    (cp.toPoint).y = cp.Y.toField / cp.T.toField := by
  unfold toPoint; rw [dif_pos h]; constructor <;> rfl

-- === Coercions ===
-- These allow using low-level types in high-level equations

/-- Coercion allowing `q + q` syntax where `q` is a ProjectivePoint. -/
noncomputable instance : Coe ProjectivePoint (Point Ed25519) where
  coe p := p.toPoint

/-- Coercion allowing comparison of `CompletedPoint` results with mathematical points. -/
noncomputable instance : Coe CompletedPoint (Point Ed25519) where
  coe p := p.toPoint

@[simp]
theorem ProjectivePoint.toPoint_eq_coe (p : ProjectivePoint) :
  p.toPoint = ↑p := rfl

@[simp]
theorem CompletedPoint.toPoint_eq_coe (p : CompletedPoint) :
  p.toPoint = ↑p := rfl

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
