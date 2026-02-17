/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Funs
import Curve25519Dalek.Types
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Edwards Point Representations

Bridge infrastructure connecting Rust implementation types to the mathematical `Point Ed25519`.
For each Edwards representation, we define `IsValid` predicates and `toPoint` conversions.

## Point Representations (Edwards-specific)

- edwards.EdwardsPoint (extended coordinates)
- edwards.affine.AffinePoint
- edwards.CompressedEdwardsY
- backend.serial.curve_models.ProjectivePoint
- backend.serial.curve_models.CompletedPoint
- backend.serial.curve_models.ProjectiveNielsPoint
-/

/-! ## Edwards Decompression -/

namespace curve25519_dalek.math

open Edwards ZMod
open Aeneas.Std Result

section EdwardsDecompression

/--
**Pure Edwards Decompression**
Recovers (x, y) from a 32-byte representation `s` according to RFC 8032 (Ed25519).
Morally: we store the point (x,y) as just the coordinate y and the sign bit, i.e. using 32-bits,
leveraging the EdCurve equation: -x² + y² = 1 + dx²y². Indeed, we can recover x just knowing y and
the sign to take on the square root to obtain x.
1. Treat the 32 bytes as a little-endian integer `s`.
2. y is the lower 255 bits (s % 2^255).
3. The sign of x is the 256th bit (s / 2^255).
-/
noncomputable def decompress_edwards_pure (bytes : Array U8 32#usize) : Option (Point Ed25519) :=
  let s := U8x32_as_Nat bytes

  -- Mathematical splitting of the 256-bit integer
  let y_int := s % (2^255)
  let sign_bit := s / (2^255) -- This is 0 or 1 because s < 2^256

  if y_int >= p then
    none
  else
    let y : ZMod p := y_int

    -- Solve for x²: x² = (y² - 1) / (dy² + 1)
    let u := y^2 - 1
    let v := d * y^2 + 1
    let x2 := u * v⁻¹

    if h : IsSquare x2 then
      let x_root := abs_edwards (Classical.choose h)
      -- Apply sign bit: if sign_bit is 1, we want the negative (odd) root
      let x := if (is_negative x_root) != (sign_bit == 1) then -x_root else x_root

      some { x := x, y := y, on_curve := by
              have hx_sq : x^2 = x2 := by
                simp only [x]
                suffices x_root ^ 2 = x2 by split_ifs <;> simpa
                have spec := Classical.choose_spec h
                rw [spec]
                dsimp [x_root]
                rw [abs_edwards_sq (Classical.choose h), pow_two]
              have hv_ne0 : v ≠ 0 := by
                intro hv
                dsimp only [v] at hv
                have h_neg : (d : ZMod p) * y^2 = -1 := eq_neg_of_add_eq_zero_left hv

                have rhs_sq : IsSquare (-1 : ZMod p) := by
                  use sqrt_m1; rw [←pow_two, sqrt_m1]; rw [← sub_eq_zero]
                  -- TODO: The tactics below cause excessive memory usage (20+ GB) because Lean's
                  -- kernel struggles with 78-digit number literals. Need to
                  -- precompute these as top-level lemmas to avoid crashing the elaborator.

                  -- change ((-1-19681161376707505956807079304988542015446066515923890162744021073123829784752 ^ 2 : ℤ) : ZMod p) = 0
                  -- rw [intCast_zmod_eq_zero_iff_dvd]
                  -- try decide
                  sorry

                have lhs_not_sq : ¬ IsSquare ((d : ZMod p) * y^2) := by
                  intro h_is_sq
                  have h_d_not_sq : ¬ IsSquare (d : ZMod p) := by
                    apply (legendreSym.eq_neg_one_iff' p).mp
                    norm_num [d, p]

                  apply h_d_not_sq
                  by_cases hy : y = 0
                  · simp only [hy, pow_two, mul_zero] at h_neg;
                    try grind
                  · rcases h_is_sq with ⟨k, hk⟩
                    use k * y⁻¹; ring_nf; field_simp [hy]; rw [← pow_two] at hk; exact hk

                rw [h_neg] at lhs_not_sq
                try grind

              simp only [hx_sq]
              dsimp [Ed25519, x2, u, v]
              simp only [neg_mul, one_mul]
              simp only [v] at hv_ne0
              rw [mul_comm] at hv_ne0
              field_simp [hv_ne0]
              ring
              }
    else
      none

end EdwardsDecompression

end curve25519_dalek.math

/-!
## AffinePoint Validity
-/

namespace curve25519_dalek.edwards.affine

open curve25519_dalek.backend.serial.u64.field
open Edwards

/--
Validity predicate for AffinePoint.
An AffinePoint contains raw field elements (x, y) which must satisfy the curve equation.
-/
@[mk_iff]
structure AffinePoint.IsValid (a : AffinePoint) : Prop where
  /-- Coordinates must be valid field elements (limbs < 2^54). -/
  x_valid : a.x.IsValid
  y_valid : a.y.IsValid
  /-- The point must satisfy the twisted Edwards equation: -x² + y² = 1 + dx²y² -/
  on_curve :
    let x := a.x.toField
    let y := a.y.toField
    Ed25519.a * x^2 + y^2 = 1 + Ed25519.d * x^2 * y^2

instance AffinePoint.instDecidableIsValid (a : AffinePoint) : Decidable a.IsValid :=
  decidable_of_iff _ (isValid_iff a).symm

/-- Convert an AffinePoint to the mathematical Point. -/
def AffinePoint.toPoint (a : AffinePoint) : Point Ed25519 :=
  if h : a.IsValid then
    { x := a.x.toField
      y := a.y.toField
      on_curve := h.on_curve }
  else 0

end curve25519_dalek.edwards.affine

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
def EdwardsPoint.toPoint' (e : EdwardsPoint) (h : e.IsValid) : Point Ed25519 :=
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
def EdwardsPoint.toPoint (e : EdwardsPoint) : Point Ed25519 :=
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

/-!
## CompressedEdwardsY Validity
-/

namespace curve25519_dalek.edwards
open curve25519_dalek.math Edwards

/--
A CompressedEdwardsY is valid if it represents a valid point on the curve.
This means the bytes must decompress successfully using the standard Ed25519 rules.
-/
def CompressedEdwardsY.IsValid (c : CompressedEdwardsY) : Prop :=
  (decompress_edwards_pure c).isSome

/--
Convert a CompressedEdwardsY to the mathematical Point.
Returns the neutral element if invalid.
-/
noncomputable def CompressedEdwardsY.toPoint (c : CompressedEdwardsY) : Point Ed25519 :=
  match decompress_edwards_pure c with
  | some P => P
  | none => 0

end curve25519_dalek.edwards

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
