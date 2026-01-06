/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
import Curve25519Dalek.Types
import Curve25519Dalek.Defs.Edwards.Curve
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Bridge Infrastructure for Edwards Curve Representations

This file bridges Rust implementation types to the mathematical `Point Ed25519`.
For each representation, we define `IsValid` predicates and `toPoint` conversions.

This file imports `Funs.lean` and `Types.lean` to access Rust implementation types.
It also imports `Edwards.EdCurve` to access the pure mathematical definitions.

## Point Representations

The Rust code uses 9 structures for representing points on the elliptic curve:

- edwards.EdwardsPoint
- ristretto.RistrettoPoint (TODO: add IsValid details and toPoint)
- ristretto.CompressedRistretto (TODO: add IsValid details and toPoint)
- backend.serial.curve_models.ProjectivePoint
- backend.serial.curve_models.CompletedPoint
- backend.serial.curve_models.ProjectiveNielsPoint
- edwards.affine.AffinePoint (TODO: add IsValid and toPoint)
- edwards.CompressedEdwardsY (TODO: add IsValid and toPoint)
- montgomery.MontgomeryPoint (TODO: add IsValid and toPoint)

The Rust code is designed so that the constructors and the various operations guarantee that the
data held by any of these is always a valid combination of coordinates. To track this we introduce
Lean predicates for each of these represenations.
-/

/-! ## Field Element Conversions -/

namespace Edwards

open curve25519_dalek CategoryTheory curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.curve_models Function ZMod

/-- Convert the 5-limb array to a field element in ZMod p. -/
def field_from_limbs (fe : backend.serial.u64.field.FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

end Edwards

/-! ## FieldElement51 Validity and Casting -/

namespace curve25519_dalek.backend.serial.u64.field
open Edwards FieldElement51

/-- Convert a FieldElement51 to the mathematical field element in ZMod p.
    This is the same as `field_from_limbs` but with dot notation support. -/
def FieldElement51.toField (fe : FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

/-! From the Rust source (field.rs):
> "In the 64-bit implementation, a `FieldElement` is represented in radix 2^51 as five u64s;
> the coefficients are allowed to grow up to 2^54 between reductions modulo p."

The bound `< 2^54` is the universal validity condition that:
- Is accepted as input by all field operations (mul, square, pow2k, sub)
-/

/-- A FieldElement51 is valid when all 5 limbs are bounded by 2^54.
    This is the bound accepted as input by field operations and encompasses
    all valid intermediate values between reductions. -/
def FieldElement51.IsValid (fe : FieldElement51) : Prop := ∀ i < 5, fe[i]!.val < 2^54

instance FieldElement51.instDecidableIsValid (fe : FieldElement51) : Decidable fe.IsValid :=
  show Decidable (∀ i < 5, fe[i]!.val < 2^54) from inferInstance

end curve25519_dalek.backend.serial.u64.field

/-! ## EdwardsPoint validity and casting -/

namespace curve25519_dalek.edwards
open curve25519_dalek.backend.serial.u64.field Edwards

/-- Validity predicate for EdwardsPoint.
    An EdwardsPoint (X, Y, Z, T) represents the affine point (X/Z, Y/Z) with T = XY/Z.
    Bounds: all coordinates < 2^53 (needed for add operations where Y+X < 2^54). -/
@[mk_iff]
structure EdwardsPoint.IsValid (e : EdwardsPoint) : Prop where
  /-- All coordinate limbs are bounded by 2^53. -/
  X_bounds : ∀ i < 5, e.X[i]!.val < 2 ^ 53
  Y_bounds : ∀ i < 5, e.Y[i]!.val < 2 ^ 53
  Z_bounds : ∀ i < 5, e.Z[i]!.val < 2 ^ 53
  T_bounds : ∀ i < 5, e.T[i]!.val < 2 ^ 53
  /-- The Z coordinate is non-zero in the field. -/
  Z_ne_zero : e.Z.toField ≠ 0
  /-- Extended coordinate relation: T = XY/Z, i.e., XY = TZ. -/
  T_relation : e.X.toField * e.Y.toField = e.T.toField * e.Z.toField
  /-- The curve equation (twisted Edwards). -/
  on_curve :
    let X := e.X.toField; let Y := e.Y.toField; let Z := e.Z.toField
    Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

instance EdwardsPoint.instDecidableIsValid (e : EdwardsPoint) : Decidable e.IsValid :=
  decidable_of_iff _ (isValid_iff e).symm

/-- Convert an EdwardsPoint to the affine point (X/Z, Y/Z).
    Requires a proof that the point is valid. -/
noncomputable def EdwardsPoint.toPoint' (e : EdwardsPoint) (h : e.IsValid) : Point Ed25519 :=
  let X := e.X.toField
  let Y := e.Y.toField
  let Z := e.Z.toField
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

/-- Convert an EdwardsPoint to the affine point (X/Z, Y/Z).
    Returns 0 if the point is not valid. -/
noncomputable def EdwardsPoint.toPoint (e : EdwardsPoint) : Point Ed25519 :=
  if h : e.IsValid then e.toPoint' h else 0

/-- Unfolding lemma: when an EdwardsPoint is valid, toPoint computes (X/Z, Y/Z). -/
theorem EdwardsPoint.toPoint_of_isValid {e : EdwardsPoint} (h : e.IsValid) :
    (e.toPoint).x = e.X.toField / e.Z.toField ∧
    (e.toPoint).y = e.Y.toField / e.Z.toField := by
  unfold toPoint
  rw [dif_pos h]
  simp only [toPoint']
  trivial

end curve25519_dalek.edwards

/-! ## RistrettoPoint Validity -/

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

/-! ## ProjectivePoint Validity and Casting -/

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
@[mk_iff]
structure ProjectivePoint.IsValid (pp : ProjectivePoint) : Prop where
  /-- All coordinate limbs are bounded by 2^52. -/
  X_bounds : ∀ i < 5, pp.X[i]!.val < 2 ^ 52
  Y_bounds : ∀ i < 5, pp.Y[i]!.val < 2 ^ 52
  Z_bounds : ∀ i < 5, pp.Z[i]!.val < 2 ^ 52
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : pp.Z.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve :
    let X := pp.X.toField; let Y := pp.Y.toField; let Z := pp.Z.toField
    Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

instance ProjectivePoint.instDecidableIsValid (pp : ProjectivePoint) : Decidable pp.IsValid :=
  decidable_of_iff _ (isValid_iff pp).symm

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

/-- Unfolding lemma: when a ProjectivePoint is valid, toPoint computes (X/Z, Y/Z). -/
theorem ProjectivePoint.toPoint_of_isValid {pp : ProjectivePoint} (h : pp.IsValid) :
    (pp.toPoint).x = pp.X.toField / pp.Z.toField ∧
    (pp.toPoint).y = pp.Y.toField / pp.Z.toField := by
  unfold toPoint; rw [dif_pos h]; constructor <;> rfl

/-! ## CompletedPoint Validity and Casting -/

open curve25519_dalek.backend.serial.u64.field in
/-- Validity predicate for CompletedPoint.
    A CompletedPoint (X, Y, Z, T) represents the affine point (X/Z, Y/T).
    For this to be on Ed25519, we need: a*(X/Z)² + (Y/T)² = 1 + d*(X/Z)²*(Y/T)²
    Clearing denominators: a*X²*T² + Y²*Z² = Z²*T² + d*X²*Y²

    All coordinates use the universal bound < 2^54. -/
@[mk_iff]
structure CompletedPoint.IsValid (cp : CompletedPoint) : Prop where
  /-- All coordinate limbs are bounded by 2^54. -/
  X_valid : cp.X.IsValid
  Y_valid : cp.Y.IsValid
  Z_valid : cp.Z.IsValid
  T_valid : cp.T.IsValid
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : cp.Z.toField ≠ 0
  /-- The T coordinate is non-zero. -/
  T_ne_zero : cp.T.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve :
    let X := cp.X.toField; let Y := cp.Y.toField
    let Z := cp.Z.toField; let T := cp.T.toField
    Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2

open curve25519_dalek.backend.serial.u64.field in
instance CompletedPoint.instDecidableIsValid (cp : CompletedPoint) : Decidable cp.IsValid :=
  decidable_of_iff _ (isValid_iff cp).symm

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

/-- Unfolding lemma: when a CompletedPoint is valid, toPoint computes (X/Z, Y/T). -/
theorem CompletedPoint.toPoint_of_isValid {cp : CompletedPoint} (h : cp.IsValid) :
    (cp.toPoint).x = cp.X.toField / cp.Z.toField ∧
    (cp.toPoint).y = cp.Y.toField / cp.T.toField := by
  unfold toPoint; rw [dif_pos h]; constructor <;> rfl

/-! ## ProjectiveNielsPoint Validity and Casting -/

/-- Validity predicate for ProjectiveNielsPoint.
    A ProjectiveNielsPoint (Y_plus_X, Y_minus_X, Z, T2d) represents a point where:
    - X = (Y_plus_X - Y_minus_X) / 2
    - Y = (Y_plus_X + Y_minus_X) / 2
    - The affine point (X/Z, Y/Z) is on Ed25519
    - T2d = 2*d*x*y*Z where x, y are the affine coordinates

    The curve equation in these coordinates (multiplied by 4 to avoid divisions):
    4*a*(Y_plus_X - Y_minus_X)²*Z² + 4*(Y_plus_X + Y_minus_X)²*Z² =
      16*Z⁴ + d*(Y_plus_X - Y_minus_X)²*(Y_plus_X + Y_minus_X)²

    Bounds: all coordinates < 2^53 (needed for mixed addition operations). -/
@[mk_iff]
structure ProjectiveNielsPoint.IsValid (pn : ProjectiveNielsPoint) : Prop where
  /-- All coordinate limbs are bounded by 2^53. -/
  Y_plus_X_bounds : ∀ i < 5, pn.Y_plus_X[i]!.val < 2 ^ 53
  Y_minus_X_bounds : ∀ i < 5, pn.Y_minus_X[i]!.val < 2 ^ 53
  Z_bounds : ∀ i < 5, pn.Z[i]!.val < 2 ^ 53
  T2d_bounds : ∀ i < 5, pn.T2d[i]!.val < 2 ^ 53
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : pn.Z.toField ≠ 0
  /-- The curve equation (scaled by 4 to avoid 1/2). -/
  on_curve :
    let YpX := pn.Y_plus_X.toField; let YmX := pn.Y_minus_X.toField; let Z := pn.Z.toField
    4 * Ed25519.a * (YpX - YmX)^2 * Z^2 + 4 * (YpX + YmX)^2 * Z^2 =
      16 * Z^4 + Ed25519.d * (YpX - YmX)^2 * (YpX + YmX)^2
  /-- T2d relation: T2d = 2*d*x*y*Z = d*(YpX² - YmX²)/(2*Z) i.e., 2*Z*T2d = d*(YpX² - YmX²). -/
  T2d_relation :
    let YpX := pn.Y_plus_X.toField; let YmX := pn.Y_minus_X.toField
    let Z := pn.Z.toField; let T2d := pn.T2d.toField
    2 * Z * T2d = Ed25519.d * (YpX^2 - YmX^2)

instance ProjectiveNielsPoint.instDecidableIsValid (pn : ProjectiveNielsPoint) : Decidable pn.IsValid :=
  decidable_of_iff _ (isValid_iff pn).symm

/-- Convert a ProjectiveNielsPoint to the affine point it represents.
    The affine coordinates are ((Y_plus_X - Y_minus_X)/(2Z), (Y_plus_X + Y_minus_X)/(2Z)). -/
noncomputable def ProjectiveNielsPoint.toPoint' (pn : ProjectiveNielsPoint) (h : pn.IsValid) :
    Point Ed25519 :=
  let YpX := pn.Y_plus_X.toField
  let YmX := pn.Y_minus_X.toField
  let Z := pn.Z.toField
  { x := (YpX - YmX) / (2 * Z)
    y := (YpX + YmX) / (2 * Z)
    on_curve := by
      have hz : Z ≠ 0 := h.Z_ne_zero
      have h2 : (2 : CurveField) ≠ 0 := by decide
      have h2z : 2 * Z ≠ 0 := mul_ne_zero h2 hz
      have h2z2 : (2 * Z)^2 ≠ 0 := pow_ne_zero 2 h2z
      have h2z4 : (2 * Z)^4 ≠ 0 := pow_ne_zero 4 h2z
      have hcurve := h.on_curve
      simp only [Ed25519] at hcurve ⊢
      simp only [div_pow]
      field_simp [h2z2, h2z4]
      ring_nf
      ring_nf at hcurve
      linear_combination hcurve }

/-- Convert a ProjectiveNielsPoint to the affine point it represents.
    Returns 0 if the point is not valid. -/
noncomputable def ProjectiveNielsPoint.toPoint (pn : ProjectiveNielsPoint) : Point Ed25519 :=
  if h : pn.IsValid then pn.toPoint' h else 0

/-- Unfolding lemma for ProjectiveNielsPoint.toPoint. -/
theorem ProjectiveNielsPoint.toPoint_of_isValid {pn : ProjectiveNielsPoint} (h : pn.IsValid) :
    (pn.toPoint).x = (pn.Y_plus_X.toField - pn.Y_minus_X.toField) / (2 * pn.Z.toField) ∧
    (pn.toPoint).y = (pn.Y_plus_X.toField + pn.Y_minus_X.toField) / (2 * pn.Z.toField) := by
  unfold toPoint
  rw [dif_pos h]
  simp only [toPoint']
  trivial

/-! ## Coercions -/

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

end curve25519_dalek.backend.serial.curve_models
