import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
import Curve25519Dalek.Types

-- Mathlib imports for elliptic curves
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Field.ZMod

import Mathlib.Algebra.Category.Ring.Basic

-- -- Mathlib imports for group structure transfer
import Mathlib.Algebra.Group.TransferInstance

-- -- Mathlib imports for field arithmetic
-- import Mathlib.Algebra.ModEq


/-!
# Ed25519: Bridge to Mathlib Weierstrass Curves

This file defines the bridge between the curve25519-dalek implementation
(Twisted Edwards curves, represented by `edwards.EdwardsPoint`)
and the mathlib elliptic curve library (Weierstrass curves).

The strategy is to establish a chain of isomorphisms:
`EdwardsPoint` ≃ `MontgomeryPoint` ≃ `WeierstrassPoint`

This allows us to leverage the powerful group theory already proven
for Weierstrass curves in mathlib and transfer it, via this chain
of equivalences, to our `EdwardsPoint` type from the Dalek repository.

## Isomorphism Chain

1.  **`EdwardsPoint` (`Types.lean`):**
    * This is the `curve25519_dalek.edwards.EdwardsPoint` struct.
    * It uses Extended Twisted Edwards Projective Coordinates `(X, Y, Z, T)`.
    * The identity element is `(0, 1, 1, 0)`.
    * This is our `SourceType`.

2.  **`MontgomeryPoint` (Mathlib):**
    * This is `curve25519_montgomery.Point`.
    * It's an affine Weierstrass point type `O | some (u, v)`
    * The curve is `By² = x³ + Ax² + x` (with `B=1`).
    * The identity element is `O` (the point at infinity).
    * The birational map `Edwards ↔ Montgomery` maps the
        Edwards identity `(0, 1)` to the Montgomery identity `O`.

3.  **`WeierstrassPoint` (Mathlib):**
    * This is `curve25519_weierstrass.Point`.
    * It's an affine Weierstrass point type `O | some (t, v)`.
    * The curve is `v² = t³ + a₄t + a₆` (short form).
    * The identity element is `O`.
    * This is our `TargetType` with a known `AddCommGroup` instance.

The `Equiv.injective.addCommGroup` pattern is then used to transfer the
`AddCommGroup` instance from `WeierstrassPoint` all the way back to
`EdwardsPoint`.
-/

universe u

open curve25519_dalek CategoryTheory WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Aeneas.Std Result


namespace Ed25519Bridge

/-!
## 1. Curve Definitions
-/

-- Use the prime 'p' from the project's Defs.lean
def CurveField := ZMod p

instance : CommRing (CurveField) := by
  unfold CurveField
  infer_instance

-- 1a. Edwards Curve
-- `ax² + y² = 1 + dx²y²`
structure EdwardsCurve (K : Type*) [CommRing K] where
  a : K
  d : K

namespace EdwardsCurve

/-- The nonsingularity condition for a twisted Edwards curve.
We require `a ≠ d` and `d ≠ 0`. -/
class IsNonsingular {K : Type*} [CommRing K] (E : EdwardsCurve K) : Prop where
  a_ne_d : E.a ≠ E.d
  d_ne_zero : E.d ≠ 0

end EdwardsCurve

/-!
## Edwards Curve25519 Instance
-/

-- We create the instance using the `a` and `d` imported from `Defs.lean`
def curve25519_edwards : EdwardsCurve CurveField where
  a := a  -- This is `def a : Int := -1` from Defs.lean, cast to CurveField
  d := d  -- This is `def d : Nat := ...` from Defs.lean, cast to CurveField

-- Prove nonsingularity for the Curve25519 instance
instance : EdwardsCurve.IsNonsingular curve25519_edwards := by
  refine ⟨?_, ?_⟩
  · -- Goal 1: a_ne_d (E.a ≠ E.d)
    simp [curve25519_edwards]
    unfold a d CurveField
    decide

  · -- Goal 2: d_ne_zero (E.d ≠ 0)
    simp [curve25519_edwards]
    unfold d CurveField
    decide


-- 1b. Montgomery Curve (Curve25519 native form)
/-- A Montgomery curve over a commutative ring `R`, defined by the
equation `By² = x³ + Ax² + x`. -/
structure MontgomeryCurve (K : Type*) [CommRing K] where
  A : K
  B : K

namespace MontgomeryCurve

/-- The nonsingularity condition for a Montgomery curve.
The discriminant `B(A² - 4)` must be non-zero. -/
class IsNonsingular {K : Type*} [CommRing K] (M : MontgomeryCurve K) : Prop where
  nonsingular : M.B * (M.A^2 - 4) ≠ 0

@[ext]
structure AffinePoint {K : Type*} [CommRing K] (M : MontgomeryCurve K) where
  x : K
  y : K
  h : M.B * y^2 = x^3 + M.A * x^2 + x

/-- A point on a Montgomery curve, which is either the point at infinity
    (`zero`) or an affine point (`some`). -/
inductive Point {K : Type*} [CommRing K] (M : MontgomeryCurve K)
  | zero
  | some (pt : M.AffinePoint)

-- Add a helpful Coe for construction
instance {K : Type*} [CommRing K] (M : MontgomeryCurve K) : Coe (M.AffinePoint)
  (Point M) := ⟨Point.some⟩

end MontgomeryCurve

/-!
## Curve25519 Instance
-/

def curve25519_montgomery : MontgomeryCurve CurveField where
  A := 486662
  B := 1

-- 3. Prove nonsingularity for the Curve25519 instance
instance : MontgomeryCurve.IsNonsingular curve25519_montgomery := by
  refine ⟨?_⟩
  simp [curve25519_montgomery]
  norm_num
  unfold CurveField
  decide

instance : Fact (Nat.Prime p) := by
  unfold p
  -- Similar to: LucasLehmer proves Mersenne primes
  -- You would prove: p is prime via certificate
  -- cf. Mathlib.NumberTheory.LucasLehmer
  sorry

instance : Field CurveField := by
  unfold CurveField
  infer_instance

-- Store constants for easy access
def M_A : CurveField := curve25519_montgomery.A
def M_B : CurveField := curve25519_montgomery.B

-- 3. Weierstrass Equivalent
-- We use the standard isomorphism for B=1:
-- `y² = x³ + Ax² + x`  → `v² = t³ + a₄t + a₆`
-- via `t = x + A/3`, `v = y`.
-- The coefficients are:
-- a₄ = (3 - A²)/3
-- a₆ = (2A³ - 9A)/27
def w_a₄ : CurveField := (3 - M_A^2) / 3
def w_a₆ : CurveField := (2 * M_A^3 - 9 * M_A) / 27

def curve25519_weierstrass : WeierstrassCurve.Affine CurveField := {
  a₁ := 0, a₂ := 0, a₃ := 0, -- Short Weierstrass form
  a₄ := w_a₄,
  a₆ := w_a₆
}

-- 4. Define Point Type Aliases
-- The `EdwardsPoint` from `Types.lean` (projective)
abbrev EdwardsPoint := curve25519_dalek.edwards.EdwardsPoint

-- Newly defined MontgomeryPoint using the def's from above
abbrev MontgomeryPoint := curve25519_montgomery.Point

-- The mathlib affine point type for our target Weierstrass curve
abbrev WeierstrassPoint :=  WeierstrassCurve.Affine.Point curve25519_weierstrass

-- Ensure the elliptic curve group law instance is synthesized for our target type.
-- This provides the necessary Add/HAdd operation.
instance : AddCommGroup WeierstrassPoint := by
  unfold WeierstrassPoint CurveField
  exact instAddCommGroup

/-!
## 2: Coordinate Transformations
-/

-- Montgomery → Weierstrass (Affine Coords)
-- (x, y) ↦ (t, v)
def montgomeryToWeierstrass_coords (x y : CurveField) : CurveField × CurveField :=
  ( x + M_A / 3,  -- t = x + A/3 (since B=1)
    y              -- v = y
  )

-- Weierstrass → Montgomery (Affine Coords)
-- (t, v) ↦ (x, y)
def weierstrassToMontgomery_coords (t v : CurveField) : CurveField × CurveField :=
  ( t - M_A / 3,  -- x = t - A/3
    v              -- y = v
  )

-- Edwards → Montgomery (Affine Coords)
-- (x, y) ↦ (u, v)
-- This map is NOT defined at the Edwards identity (0, 1).
def edwardsToMontgomery_coords (x y : CurveField) : CurveField × CurveField :=
  let u := (1 + y) / (1 - y)
  let v := u / x
  (u, v)

-- Montgomery → Edwards (Affine Coords)
-- (u, v) ↦ (x, y)
-- This map is NOT defined at the Montgomery identity (O).
def montgomeryToEdwards_coords (u v : CurveField) : CurveField × CurveField :=
  ( u / v,            -- x
    (u - 1) / (u + 1) -- y
  )

/-!
## 3: Prove Curve Preservation (Structural)
-/

-- These theorems prove that the coordinate maps preserve the curve equations.
-- This is necessary to show the point-level maps are well-defined.

theorem montgomery_to_weierstrass_on_curve (x y : CurveField)
  (h : y ^ 2 = x ^ 3 + M_A * x ^ 2 + x) : -- B=1
  let (t, v) := montgomeryToWeierstrass_coords x y
  v^2 = t^3 + w_a₄ * t + w_a₆ := by
  simp [montgomeryToWeierstrass_coords, w_a₄, w_a₆, h]
  field_simp [
    (by unfold CurveField; decide : (3 : CurveField) ≠ 0),
    (by unfold CurveField; decide : (27 : CurveField) ≠ 0)
  ]
  ring_nf

theorem weierstrass_to_montgomery_on_curve (t v : CurveField)
  (h : v ^ 2 = t ^ 3 + w_a₄ * t + w_a₆) :
  let (x, y) := weierstrassToMontgomery_coords t v
  y^2 = x^3 + M_A * x^2 + x := by
  simp [weierstrassToMontgomery_coords, w_a₄, w_a₆, h]
  field_simp [
    (by unfold CurveField; decide : (3 : CurveField) ≠ 0),
    (by unfold CurveField; decide : (27 : CurveField) ≠ 0)
  ]
  ring_nf

-- The Edwards ↔ Montgomery birational equivalence is a standard
-- but very complex proof. For now we'll use a (`sorry`).
theorem edwards_to_montgomery_on_curve (x y : CurveField)
  (h_curve : curve25519_edwards.a * x ^ 2 + y ^ 2 = 1 + curve25519_edwards.d * x ^ 2 * y ^ 2)
  (h_denom_y : 1 - y ≠ 0) (h_denom_x : x ≠ 0) :
  let (u, v) := edwardsToMontgomery_coords x y
  curve25519_montgomery.B * v^2 = u^3 + curve25519_montgomery.A * u^2 + u := by
  -- probably we need to use IsoOfJ in mathlib Elliptic curves at some point.
  sorry -- TODO: This is a complex polynomial identity proof.

theorem montgomery_to_edwards_on_curve (u v : CurveField)
  (h_curve : curve25519_montgomery.B * v ^ 2 = u ^ 3 + curve25519_montgomery.A * u ^ 2 + u)
  (h_denom_v : v ≠ 0) (h_denom_u : u + 1 ≠ 0) :
  let (x, y) := montgomeryToEdwards_coords u v
  curve25519_edwards.a * x^2 + y^2 = 1 + curve25519_edwards.d * x^2 * y^2 := by
  sorry -- TODO: Inverse of the above.

/-!
## 4: Point Type Equivalences
-/

-- 4.1. Point type transformations
-- These functions lift the coordinate maps to the point types,
-- correctly mapping the identity elements (O ↔ O).

-- Montgomery ↔ Weierstrass
def montgomeryPointToWeierstrass (P : MontgomeryPoint) : WeierstrassPoint :=
  match P with
  | .zero =>
    WeierstrassCurve.Affine.Point.zero

  | .some hP => by
    have h_mont_simple : hP.y ^ 2 = hP.x ^ 3 + M_A * hP.x ^ 2 + hP.x := by
        have h := hP.h
        simp only [curve25519_montgomery, one_mul, M_A] at h ⊢
        exact h

    have h_eq : (montgomeryToWeierstrass_coords hP.x hP.y).2 ^ 2 =
                (montgomeryToWeierstrass_coords hP.x hP.y).1 ^ 3 +
                w_a₄ * (montgomeryToWeierstrass_coords hP.x hP.y).1 + w_a₆ := by
      exact montgomery_to_weierstrass_on_curve hP.x hP.y h_mont_simple

    refine WeierstrassCurve.Affine.Point.some (x := (montgomeryToWeierstrass_coords hP.x hP.y).1)
      (y := (montgomeryToWeierstrass_coords hP.x hP.y).2) ?h

    -- 3. The goal is now `⊢ (curve25519_weierstrass).Nonsingular ...`
    case h =>
      refine ⟨?left, ?right⟩

      -- 4. Solve the `left` goal
      case left =>
        simp only [
          WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.polynomial,
          curve25519_weierstrass,
          Polynomial.evalEval, Polynomial.eval_X, Polynomial.eval_C,
          Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
          zero_mul, add_zero, --map_zero
        ]
        rw [sub_eq_zero]
        exact h_eq

      -- 5. Solve the `right` goal
      case right =>
        simp only [
          WeierstrassCurve.Affine.polynomialX, WeierstrassCurve.Affine.polynomialY,
          curve25519_weierstrass,
          Polynomial.evalEval, Polynomial.eval_X, Polynomial.eval_C,
          Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
          zero_mul, add_zero, --map_zero,
          montgomeryToWeierstrass_coords, w_a₄
        ]
        field_simp [(by unfold CurveField; decide : (3 : CurveField) ≠ 0)]
        --field_simp [(by unfold CurveField; decide : (3 : CurveField) ≠ 0)]

        simp only [M_A]
        right

        apply mul_ne_zero
        · unfold CurveField
          decide
        · -- Goal 2: ⊢ hP.y ≠ 0
          sorry -- TODO: Prove hP.y ≠ 0 from curve nonsingularity


def weierstrassPointToMontgomery (P : WeierstrassPoint) : MontgomeryPoint :=
  match P with
  | .zero => .zero -- Identity maps to identity
  | @WeierstrassCurve.Affine.Point.some _ _ _ t v hP => by
    --have h_weierstrass_eq_r := hP.right
    have h_weierstrass_eq_l := hP.left
    simp only [
        WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.polynomial,
        curve25519_weierstrass,
        Polynomial.evalEval, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        zero_mul, add_zero, --map_zero,
        sub_eq_zero
      ] at h_weierstrass_eq_l

    let (x, y) := weierstrassToMontgomery_coords t v

    have h_montgomery_eq : curve25519_montgomery.B * y^2 = x^3 + curve25519_montgomery.A * x^2 + x := by
      simp only [curve25519_montgomery, one_mul]
      --rw [montgomery_to_weierstrass_on_curve t v _] at h_weierstrass_eq_l

      sorry

    let mont_affine_pt : curve25519_montgomery.AffinePoint := {
      x := x,
      y := y,
      h := h_montgomery_eq
    }
    exact .some mont_affine_pt
/-!
## 5. Math version of Edwards Points
-/

-- Define a version of EdwardsPoint aligned with our Field structure
structure EdwardsPointMath where
  X : CurveField
  Y : CurveField
  Z : CurveField
  T : CurveField

-- Equivalence for the Dalek type and the Math type
def dalekToMathEquiv : EdwardsPoint ≃ EdwardsPointMath := sorry

-- EdwardsMath ↔ Montgomery: Coordinate transformation functions (now using total functions on CurveField)
def edwardsMathPointToMontgomery (P_ed : EdwardsPointMath) : MontgomeryPoint :=
  sorry

def montgomeryToEdwardsMathPoint (P_mont : MontgomeryPoint) : EdwardsPointMath :=
  sorry

-- Establish the EdwardsMath ↔ Montgomery equivalence
def edwardsMathMontgomeryEquiv : EdwardsPointMath ≃ MontgomeryPoint where
  toFun := edwardsMathPointToMontgomery
  invFun := montgomeryToEdwardsMathPoint
  left_inv := by sorry
  right_inv := by sorry


-- 7. Establish equivalences
def montgomeryWeierstrassEquiv : MontgomeryPoint ≃ WeierstrassPoint where
  toFun := montgomeryPointToWeierstrass
  invFun := weierstrassPointToMontgomery
  left_inv := by
    -- This follows from the fact that the coord maps are inverses
    intro P
    cases P
    · rfl
    · simp only [weierstrassPointToMontgomery, montgomeryPointToWeierstrass,
      montgomeryToWeierstrass_coords, weierstrassToMontgomery_coords, add_sub_cancel_right]
  right_inv := by
    intro P
    cases P
    · rfl
    · simp only [montgomeryPointToWeierstrass, weierstrassPointToMontgomery,
      weierstrassToMontgomery_coords, montgomeryToWeierstrass_coords, sub_add_cancel]

-- 8. Chained equivalence (Math-Aligned EdwardsPointMath ↔ WeierstrassPoint)
def edwardsWeierstrassEquivMath : EdwardsPointMath ≃ WeierstrassPoint :=
  edwardsMathMontgomeryEquiv.trans montgomeryWeierstrassEquiv

-- The ultimate equivalence from the Dalek type to the final target
def edwardsWeierstrassEquiv : EdwardsPoint ≃ WeierstrassPoint :=
  dalekToMathEquiv.trans edwardsWeierstrassEquivMath

/-!
## 6. Group Structure Transfer
-/

def MontgomeryPoint.add (P Q : MontgomeryPoint) : MontgomeryPoint :=
  montgomeryWeierstrassEquiv.symm (montgomeryWeierstrassEquiv P + montgomeryWeierstrassEquiv Q)

-- Define the Add instance on MontgomeryPoint using the transferred operation.
instance : Add MontgomeryPoint where
  add := MontgomeryPoint.add

instance : Zero MontgomeryPoint where
  zero := MontgomeryCurve.Point.zero

instance : AddCommGroup MontgomeryPoint := by
  exact Equiv.addCommGroup montgomeryWeierstrassEquiv

-- 9. Prove addition is preserved through transformations
theorem montgomery_weierstrass_addition_preserved (p q : MontgomeryPoint) :
  montgomeryWeierstrassEquiv (p + q) =
  montgomeryWeierstrassEquiv p + montgomeryWeierstrassEquiv q := by
  sorry -- TODO

-- 1. Define addition on EdwardsPointMath via operation transfer
def EdwardsPointMath.add (P Q : EdwardsPointMath) : EdwardsPointMath :=
  edwardsWeierstrassEquivMath.symm (edwardsWeierstrassEquivMath P + edwardsWeierstrassEquivMath Q)

instance : Add EdwardsPointMath where
  add := EdwardsPointMath.add

instance : Zero EdwardsPointMath where
  zero := edwardsWeierstrassEquivMath.symm WeierstrassCurve.Affine.Point.zero

def edwardsWeierstrassAddEquivMath : EdwardsPointMath ≃+ WeierstrassPoint :=
  AddEquiv.mk edwardsWeierstrassEquivMath (by
    intro P Q
    dsimp only [HAdd.hAdd, Add.add, EdwardsPointMath.add]
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]
  )

instance : AddCommGroup EdwardsPointMath := edwardsWeierstrassAddEquivMath.toEquiv.addCommGroup

instance : AddCommGroup EdwardsPoint := Equiv.addCommGroup dalekToMathEquiv

-- 1. Redefine addition on EdwardsPointMath (via MontgomeryPoint)
def EdwardsPointMath.add_via_montgomery (P Q : EdwardsPointMath) : EdwardsPointMath :=
  edwardsMathMontgomeryEquiv.symm (edwardsMathMontgomeryEquiv P + edwardsMathMontgomeryEquiv Q)

-- 2. New AddEquiv Definition: EdwardsMath ↔ Montgomery
def edwardsMathMontgomeryAddEquiv : EdwardsPointMath ≃+ MontgomeryPoint :=
  AddEquiv.mk edwardsMathMontgomeryEquiv (by
    intro P Q
    simp only [Equiv.toFun_as_coe]
    dsimp only [HAdd.hAdd, Add.add]
    exact (Equiv.apply_eq_iff_eq_symm_apply edwardsMathMontgomeryEquiv).mpr rfl
  )

-- 3. The theorem proves the equivalence is an AddEquiv (now recast for the final Dalek type)
theorem edwards_montgomery_addition_preserved (p q : EdwardsPointMath) :
  edwardsMathMontgomeryEquiv (p + q) =
  edwardsMathMontgomeryEquiv p + edwardsMathMontgomeryEquiv q := by
  exact edwardsMathMontgomeryAddEquiv.map_add p q

/-!
## 7. A Math Doubling Spec Thm
-/

-- Placeholder: This is what P.double_impl must encapsulate:
def EdwardsPointMath.double_impl (P : EdwardsPointMath) :
  Result EdwardsPointMath :=
  -- This requires: dalekToMathEquiv.invFun P → EdwardsPoint.double → dalekToMathEquiv
  -- (This represents the execution of the low-level hardware operation)
  sorry

-- It performs the required safe projection, extracting the successful value or defaulting to Zero.
def EdwardsPointMath.safe_extract (P_res : Result EdwardsPointMath) : EdwardsPointMath :=
  match P_res with
  | ok r => r
  | fail _ => 0 -- Default to the identity element (0) upon failure.
  | div => 0   -- Explicitly handle the 'div' (division/panic) failure state revealed by the elaborator.

-- The high-level function that executes the doubling implementation and safely extracts the result.
def EdwardsPointMath.double_result (P : EdwardsPointMath) : EdwardsPointMath := by
  sorry

-- Fix for HMul/Scalar Multiplication:
-- We define this instance explicitly to resolve the HMul typeclass dependency for '2 * P'.
instance : HMul ℕ EdwardsPointMath EdwardsPointMath where
  -- Redirect the multiplication notation (*) to the scalar multiplication operation (•).
  hMul := SMul.smul

-- Theorem asserting the low-level implementation (double_impl) succeeds and
-- is equivalent to the high-level group operation (P + P).
-- NOTE: This theorem encapsulates the massive algebraic complexity of the Dalek verification.
theorem double_eq_add (P : EdwardsPointMath) :
  P.double_impl = ok (P + P) := by
  sorry -- The core verification proof lives here.

-- The final, clean, high-level specification.
-- This theorem asserts that the mapped result of the low-level double equals the mapped result
-- of scalar multiplication by two (2 * P), which holds by the group axioms.
theorem double_spec_math (P : EdwardsPointMath) :
  edwardsWeierstrassEquivMath (P.double_result) = edwardsWeierstrassEquivMath (2 * P) := by
  unfold EdwardsPointMath.double_result

  -- -- Substitute P.double_impl with its successful group law definition (P + P).
  -- rw [double_eq_add]
  -- simp only [EdwardsPointMath.safe_extract]
  -- simp only [nsmul_eq_mul, two_nsmul]
  sorry






/-

/-!
## Phase 6: Condition Verification & Demonstration for Birational Mappings

What is the actual purpose of those three condition theorems?
These conditions are typically prerequisites for proving the map from:
 Montgomery $\leftrightarrow$ Weierstrass
is a valid birational map over specific fields or points. Specifically, they relate to:
 · 2-Torsion: Conditions 2 and 3 relate to the existence and nature of the curve's 2-torsion points,
   often required to prove the canonical map is well-defined.
  · Isomorphism: They are necessary for establishing that the curve algebraically satisfies the
    requirements for the elliptic curve group structure and the specific birational equivalence
    being used
-/

-- These theorems are requested to prove the validity of the
-- general W → M  birational transformation.

theorem weierstrass_to_montgomery_condition_1 :
  -- Order divisibility by 4
  -- This is a known property of Curve25519.
  sorry

theorem weierstrass_to_montgomery_condition_2 :
  -- `z³ + a₄z + a₆ = 0` has at least one root α ∈ ZMod p
  -- As `t = x + A/3`, the inverse is `x = t - A/3`.
  -- The root `α` is `A/3`.
  ∃ α : CurveField, α^3 + w_a₄ * α + w_a₆ = 0 := by
    use (M_A / 3)
    -- This polynomial identity was proven implicitly in
    -- `montgomery_to_weierstrass_on_curve`.
    field_simp [w_a₄, w_a₆, three_ne_zero, twentyseven_ne_zero]
    ring

theorem weierstrass_to_montgomery_condition_3 (α : CurveField)
  (h : α^3 + w_a₄ * α + w_a₆ = 0) :
  -- `3α² + a₄` must be a quadratic residue (IsSquare)
  -- This is required for `s = (3α² + a₄)^(-1/2)` to exist.
  -- In our case, `α = A/3` and `B=1`.
  -- `3(A/3)² + a₄ = 3(A²/9) + (3-A²)/3 = A²/3 + (3-A²)/3 = 3/3 = 1`.
  -- `1` is always a square.
  IsSquare (3 * α^2 + w_a₄) := by
    -- We can't assume `α = M_A / 3` from `h`, so this is harder.
    -- But if we use the *specific* root:
    have α_spec : (M_A / 3)^3 + w_a₄ * (M_A / 3) + w_a₆ = 0 := by
      field_simp [w_a₄, w_a₆, three_ne_zero, twentyseven_ne_zero]; ring
    -- We only need to show it for *one* root.
    -- Let's just prove the term is `1`.
    have h_alpha : α = M_A / 3 := by sorry -- TODO: Prove root is unique or this holds
    simp [h_alpha, w_a₄]
    field_simp [three_ne_zero]
    ring
    -- The goal is `IsSquare 1`, which is true.
    use 1
    simp

-- Demonstration of applying a mathlib theorem
example (p : EdwardsPoint) : p + p = (2 : ℤ) • p := by
  -- This proof holds *because* we just defined
  -- `AddCommGroup EdwardsPoint` and its `zsmul`.
  -- This is a standard theorem in `AddCommGroup`.
  exact AddCommGroup.two_zsmul p


-/

end Ed25519Bridge
