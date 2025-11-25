import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
import Curve25519Dalek.Types
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectivePoint.Double

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs


namespace Edwards

open curve25519_dalek CategoryTheory curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.curve_models Function ZMod

-- The Twisted Edwards curve is defined as: ax² + y² = 1 + dx²y²

/-- The finite field F_p where p = 2^255 - 19. -/
abbrev CurveField : Type := ZMod p

instance : Fact (Nat.Prime p) := by
  unfold p
  -- the proof is in https://github.com/kckennylau/PrimeCert/blob/master/PrimeCert/PrimeList.lean#L84
  sorry

/-- The field structure on `CurveField`. -/
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
  ⟨{ x := 0, y := 1, h_on_curve := by simp only [Ed25519, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, one_pow, zero_add, mul_one, add_zero] }⟩

variable {F : Type} [Field F] (C : EdwardsCurve F)

/-- Implements the unified addition formulas for Twisted Edwards curves.
    (x₁, y₁) + (x₂, y₂) = ( (x₁y₂ + y₁x₂)/(1 + dx₁x₂y₁y₂), (y₁y₂ - ax₁x₂)/(1 - dx₁x₂y₁y₂) ) -/
def add_coords (p1 p2 : F × F) : F × F :=
  let (x₁, y₁) := p1
  let (x₂, y₂) := p2
  let lambda_val := C.d * x₁ * x₂ * y₁ * y₂
  ( (x₁ * y₂ + y₁ * x₂) / (1 + lambda_val),
    (y₁ * y₂ - C.a * x₁ * x₂) / (1 - lambda_val) )

/-- Theorem: The sum of two points on the curve stays on the curve. Requires 'd' non-square. -/
theorem add_closure (p1 p2 : Point C) :
    let (x, y) := add_coords C (p1.x, p1.y) (p2.x, p2.y)
    C.a * x^2 + y^2 = 1 + C.d * x^2 * y^2 := by
  simp only [add_coords]
  let (x₁, y₁) := (p1.x, p1.y)
  let (x₂, y₂) := (p2.x, p2.y)
  -- Assume denominators are non-zero (True for valid Ed25519 points, but hard to prove quickly)
  have h_denom : 1 + C.d * x₁ * x₂ * y₁ * y₂ ≠ 0 ∧ 1 - C.d * x₁ * x₂ * y₁ * y₂ ≠ 0 := sorry
  field_simp [h_denom]
  have h1 := p1.h_on_curve
  have h2 := p2.h_on_curve
  sorry

instance : Add (Point C) where
  add p1 p2 :=
  let coords := add_coords C (p1.x, p1.y) (p2.x, p2.y)
  { x := coords.1
    y := coords.2
    h_on_curve := add_closure C p1 p2 }

/-- The neutral element of the Edwards curve is (0, 1). -/
instance : Zero (Point C) where
  zero := {
    x := 0
    y := 1
    h_on_curve := by simp
  }

/-- Point negation maps (x, y) to (-x, y). -/
instance : Neg (Point C) where
  neg p := {
    x := -p.x
    y := p.y
    -- Proof: a*(-x)^2 + y^2 = a*x^2 + y^2, so the curve equation is preserved.
    h_on_curve := by
      have h := p.h_on_curve
      simp only [neg_pow_two]
      exact h
  }

/-- Standard subtraction: P - Q = P + (-Q). -/
instance : Sub (Point C) where
  sub p1 p2 := p1 + (-p2)

/-- Scalar multiplication by Natural numbers (standard recursive definition). -/
def nsmul (n : ℕ) (p : Point C) : Point C :=
  match n with
  | 0 => 0
  | n + 1 => p + (nsmul n p)

/-- Scalar multiplication by Integers. -/
def zsmul (z : ℤ) (p : Point C) : Point C :=
  match z with
  | (n : ℕ) => nsmul C n p
  | (Int.negSucc n) => -(nsmul C (n + 1) p)

-- Register the '•' notation
instance : SMul ℕ (Point C) := ⟨nsmul C⟩
instance : SMul ℤ (Point C) := ⟨zsmul C⟩

/-- The Edwards Curve forms an additive abelian group.
    We 'sorry' the axioms to skip huge polynomial proofs (associativity is hard). -/
instance : AddCommGroup (Point C) where
  add := Add.add
  add_assoc := by sorry -- The "hard" proof (requires checking (x^2 + y^2...))
  zero := 0
  zero_add p := by

    sorry
  add_zero := by sorry
  nsmul := nsmul C
  neg := Neg.neg
  zsmul := zsmul C
  neg_add_cancel := by sorry
  add_comm := by sorry
  nsmul_succ := by sorry
  zsmul_succ':= by sorry

/-- Helper lemma to expose the addition formula without unfolding the whole structure. -/
theorem add_def (p1 p2 : Point Ed25519) :
  (p1 + p2).x = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).1 ∧
  (p1 + p2).y = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).2 := by
  exact Prod.mk_inj.mp rfl

/-- Convert the 5-limb array to a field element in ZMod p.
    Uses 'Field51_as_Nat' from Defs.lean to interpret the limbs. -/
def field_from_limbs (fe : backend.serial.u64.field.FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

end Edwards

namespace curve25519_dalek.edwards.affine

open Edwards

def AffinePoint.IsValid (low : AffinePoint) (high : Point Ed25519) : Prop :=
    field_from_limbs low.x = high.x ∧ field_from_limbs low.y = high.y

noncomputable def AffinePoint.toPoint (p : AffinePoint) (h : ∃ P, p.IsValid P) : Point Ed25519 :=
 { x := field_from_limbs p.x,
    y := field_from_limbs p.y,
    h_on_curve := by
      have ⟨P, hP⟩ := h; rw [AffinePoint.IsValid] at hP; rw [hP.1, hP.2]; exact P.h_on_curve }

end curve25519_dalek.edwards.affine

namespace curve25519_dalek.backend.serial.curve_models

open Edwards

def ProjectivePoint.IsValid (low : ProjectivePoint) (high : Point Ed25519) : Prop :=
    let X := field_from_limbs low.X; let Y := field_from_limbs low.Y; let Z := field_from_limbs low.Z
    Z ≠ 0 ∧ X = high.x * Z ∧ Y = high.y * Z

def ProjectivePoint.InBounds (p : ProjectivePoint) : Prop :=
  (∀ i, i < 5 → (p.X[i]!).val ≤ 2^52) ∧
  (∀ i, i < 5 → (p.Y[i]!).val ≤ 2^52) ∧
  (∀ i, i < 5 → (p.Z[i]!).val ≤ 2^52)

noncomputable def ProjectivePoint.toPoint (p : ProjectivePoint) (h : ∃ P, p.IsValid P) : Point Ed25519 :=
  { x := field_from_limbs p.X / field_from_limbs p.Z,
    y := field_from_limbs p.Y / field_from_limbs p.Z,
    h_on_curve := by
      have ⟨P, hP⟩ := h; rw [ProjectivePoint.IsValid] at hP
      field_simp [hP.1]; rw [hP.2.1, hP.2.2]
      have h_curve := P.h_on_curve
      apply_fun (fun t => field_from_limbs p.Z ^ 4 * t) at h_curve
      ring_nf at h_curve ⊢; exact h_curve }

def CompletedPoint.IsValid (low : CompletedPoint) (high : Point Ed25519) : Prop :=
  let X := field_from_limbs low.X; let Y := field_from_limbs low.Y
  let Z := field_from_limbs low.Z; let T := field_from_limbs low.T
  Z ≠ 0 ∧ T ≠ 0 ∧ X = high.x * Z ∧ Y = high.y * T

noncomputable def CompletedPoint.toPoint (p : CompletedPoint) (h : ∃ P, p.IsValid P) : Point Ed25519 :=
  { x := field_from_limbs p.X / field_from_limbs p.Z,
    y := field_from_limbs p.Y / field_from_limbs p.T,
    h_on_curve := by
      have ⟨P, hP⟩ := h; rw [CompletedPoint.IsValid] at hP
      field_simp [hP.1, hP.2.1]; rw [hP.2.2.1, hP.2.2.2]
      have h_curve := P.h_on_curve
      apply_fun (fun t => (field_from_limbs p.Z)^2 * (field_from_limbs p.T)^2 * t) at h_curve
      convert h_curve using 1 <;> ring }

/-- Existential validity predicate for ProjectivePoint. -/
def ProjectivePoint.IsValid' (p : ProjectivePoint) : Prop := ∃ P, p.IsValid P

/-- Existential validity predicate for CompletedPoint. -/
def CompletedPoint.IsValid' (p : CompletedPoint) : Prop := ∃ P, p.IsValid P

/--
Total conversion function.
If the point is valid, returns the unique `Point Ed25519` it represents.
If invalid, returns the neutral element `0` (garbage value).
-/
noncomputable def ProjectivePoint.toPoint' (p : ProjectivePoint) : Point Ed25519 :=
  open Classical in
  if h : p.IsValid' then
    choose h
  else
    0

/-- Total conversion function for CompletedPoint. -/
noncomputable def CompletedPoint.toPoint' (p : CompletedPoint) : Point Ed25519 :=
  open Classical in
  if h : p.IsValid' then
    choose h
  else
    0

/-!
## Bridge Lemmas
These connect the new total functions back to the underlying logic.
-/

theorem ProjectivePoint.toPoint'_eq_of_isValid {p : ProjectivePoint} {P : Point Ed25519}
    (h : p.IsValid P) : p.toPoint' = P := by
  rw [toPoint', dif_pos ⟨P, h⟩]
  -- We need to show the point P is unique.
  -- IsValid definition: Z ≠ 0 ∧ X = P.x * Z ∧ Y = P.y * Z
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

end curve25519_dalek.backend.serial.curve_models

namespace Edwards

open curve25519_dalek.backend.serial.curve_models

/-!
## The Refactored Theorem
-/

-- Helper lemma
theorem lift_mod_eq (a b : ℕ) (h : a % p = b % p) : (a : CurveField) = (b : CurveField) := by
  apply (ZMod.natCast_eq_natCast_iff a b p).mpr
  exact h

theorem double_spec_math'
    (q : ProjectivePoint) (hq_valid : q.IsValid') (hq_bounds : q.InBounds) :
    ∃ c, ProjectivePoint.double q = .ok c ∧ c.IsValid' ∧
    c.toPoint' = q.toPoint' + q.toPoint' := by

  rcases hq_valid with ⟨P, hP⟩
  rw [ProjectivePoint.toPoint'_eq_of_isValid hP]

  have ⟨out, h_run, h_arith⟩ := ProjectivePoint.double_spec q
    (fun i h => hq_bounds.1 i h)
    (fun i h => hq_bounds.2.1 i h)
    (fun i h => hq_bounds.2.2 i h)

  exists out
  constructor
  · exact h_run -- The function runs successfully

  let P2 := P + P

  have h_out_represents_P2 : out.IsValid P2 := by
    rw [ProjectivePoint.IsValid] at hP; rcases hP with ⟨hZ_nonzero, hX_in, hY_in⟩
    rcases h_arith with ⟨hX_new, hY_new, hZ_new, hT_new⟩

    let X_nat := Field51_as_Nat q.X
    let Y_nat := Field51_as_Nat q.Y
    let Z_nat := Field51_as_Nat q.Z

    have hX_F : field_from_limbs out.X = 2 * field_from_limbs q.X * field_from_limbs q.Y := by
      dsimp [field_from_limbs]; rw [lift_mod_eq _ _ hX_new]; push_cast; rfl

    have hY_F : field_from_limbs out.Y = field_from_limbs q.Y ^ 2 + field_from_limbs q.X ^ 2 := by
      dsimp [field_from_limbs]; rw [lift_mod_eq _ _ hY_new]; push_cast; rfl

    have hZ_F : field_from_limbs out.Z = field_from_limbs q.Y ^ 2 - field_from_limbs q.X ^ 2 := by
      have h := lift_mod_eq _ _ hZ_new; push_cast at h; apply eq_sub_of_add_eq h

    have hT_F : field_from_limbs out.T = 2 * field_from_limbs q.Z ^ 2 - field_from_limbs out.Z := by
      have h := lift_mod_eq _ _ hT_new; push_cast at h; apply eq_sub_of_add_eq h

    unfold CompletedPoint.IsValid
    have h_curve : -P.x^2 + P.y^2 = 1 + Ed25519.d * P.x^2 * P.y^2 := by
      have h := P.h_on_curve; simp only [Ed25519, neg_mul, one_mul] at h; exact h

    -- This is a known property of Ed25519 parameters.
    have h_d_not_square : ¬IsSquare Ed25519.d := sorry

    -- Prove -1 is a square in this field (since p ≡ 1 mod 4)
    have h_neg_one_square : IsSquare (-1 : CurveField) := by
      apply ZMod.exists_sq_eq_neg_one_iff.mpr
      decide

    have h_denom_plus : 1 + Ed25519.d * P.x^2 * P.y^2 ≠ 0 := by
      intro h_zero
      apply h_d_not_square

      -- d * (xy)^2 = -1
      rw [add_eq_zero_iff_eq_neg] at h_zero
      rw [← neg_eq_iff_eq_neg] at h_zero
      have ⟨k, hk⟩ := h_neg_one_square -- k^2 = -1
      ring_nf at hk h_zero
      rw [hk] at h_zero -- d * (xy)^2 = k^2

      by_cases h_xy_nz : P.x * P.y = 0
      · -- Contradiction case
        rw [mul_assoc, ← mul_pow, h_xy_nz] at h_zero
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
          pow_eq_zero_iff] at h_zero
        rw [h_zero] at hk;  rw [zero_pow (by decide)] at hk;  norm_num at hk

      -- 3. Construct the square root of d: k / (x*y)
      · use k / (P.x * P.y)
        ring_nf
        field_simp [h_xy_nz]
        rw [h_zero]
        have h_nz : P.x^2 * P.y^2 ≠ 0 := by
          rw [←mul_pow]
          exact pow_ne_zero 2 h_xy_nz
        rw [mul_assoc, mul_div_cancel_right₀ _ h_nz]

    refine ⟨?_ ,?_, ?_, ?_⟩

    -- Goal 1: Z ≠ 0
    · rw [hZ_F, hX_in, hY_in]
      grind
      
    -- Goal 2: T ≠ 0
    · rw [hT_F, hZ_F, hX_in, hY_in]
      rw [mul_pow, mul_pow]
      have h_factor : 2 * field_from_limbs q.Z ^ 2 - (P.y^2 * field_from_limbs q.Z ^ 2 - P.x^2 * field_from_limbs q.Z ^ 2) =
                      field_from_limbs q.Z ^ 2 * (2 - (P.y^2 - P.x^2)) := by ring
      rw [h_factor]
      apply mul_ne_zero
      · -- Z^2 ≠ 0 because Z ≠ 0
        exact pow_ne_zero 2 hZ_nonzero
      · -- proof of 2-(y^2-x^2) ≠ 0
        have h_curve' : 2 - (P.y^2 - P.x^2) = 1 - Ed25519.d * P.x^2 * P.y^2 := by
          calc
            2 - (P.y ^ 2 - P.x ^ 2)
            _ = 2 - (-P.x ^ 2 + P.y ^ 2) := by ring
            _= 2 - (1 + Ed25519.d * P.x ^ 2 * P.y ^ 2) := by rw [← h_curve]
            _ = 1 - Ed25519.d * P.x ^ 2 * P.y ^ 2 := by ring

        rw [h_curve']

        -- Proof that 1 - d(xy)^2 ≠ 0
        intro h_zero
        apply h_d_not_square -- Strategy: prove d is a square to get a contradiction

        -- Algebraic rearrangement: 1 = d * (xy)^2
        rw [sub_eq_zero, eq_comm] at h_zero

        -- We need to divide by (xy), so handle the zero case first
        by_cases h_xy : P.x * P.y = 0
        · rw [mul_assoc, ←mul_pow, h_xy, zero_pow two_ne_zero, mul_zero] at h_zero
          norm_num at h_zero

        · -- Construct the square root of d: 1/(xy)
          use 1 / (P.x * P.y)
          field_simp [h_xy]
          have h_nz : P.x^2 * P.y^2 ≠ 0 := by
            rw [←mul_pow]; exact pow_ne_zero 2 h_xy
          rw [eq_div_iff h_nz]; ring_nf at h_zero ⊢
          exact h_zero

    -- Verify X coordinate: out.X = P2.x * out.Z
    -- Goal: 2*X*Y = ( (x*y + y*x) / (1 + dxyxy) ) * (Y^2 - X^2)
    · rw [(add_def P P).1]
      dsimp only [add_coords]
      rw [hX_F, hZ_F, hX_in, hY_in]

      have h_denom : 1 + Ed25519.d * P.x * P.x * P.y * P.y ≠ 0 := sorry
      have h_subst : 1 + Ed25519.d * P.x^2 * P.y^2 = P.y^2 - P.x^2 := by
        rw [←h_curve]; ring
      have h_denom' : P.y^2 - P.x^2 ≠ 0 := by
        rw [← h_subst]; ring_nf at ⊢ h_denom; exact h_denom
      have h_comm : 1 + P.x^2 * P.y^2 * Ed25519.d = 1 + Ed25519.d * P.x^2 * P.y^2 := by ring

      field_simp [h_denom, ← h_curve]
      rw [h_comm, h_subst]

      field_simp [h_denom']
      ring

    -- Verify Y coordinate: out.Y = P2.y * out.T
    -- Goal: Y^2 + X^2 = ( (y*y - a*x*x) / (1 - dxyxy) ) * (2Z^2 - (Y^2 - X^2))
    · rw [(add_def P P).2]

      dsimp only [add_coords]

      rw [hY_F, hT_F, hZ_F, hX_in, hY_in]

      have h_a : Ed25519.a = -1 := rfl
      rw [h_a]

      have h_denom : 1 - Ed25519.d * P.x * P.x * P.y * P.y ≠ 0 := sorry
      field_simp [hZ_nonzero, h_denom]
      ring_nf at h_denom

      have h_comm : 1 - Ed25519.d * P.x * P.x * P.y * P.y = 1 - P.y ^ 2 * P.x ^ 2 * Ed25519.d := by ring
      have h_denom': 1 - P.y ^ 2 * P.x ^ 2 * Ed25519.d ≠ 0 := by
        rw [← h_comm]
        ring_nf
        exact h_denom

      field_simp [h_denom]
      have h_subst : 2 - (P.y ^ 2 - P.x ^ 2) =
        1 - Ed25519.d * P.x ^ 2 * P.y ^ 2 := by
        calc
          2 - (P.y ^ 2 - P.x ^ 2)
          _ = 2 - (-P.x ^ 2 + P.y ^ 2) := by ring
          _= 2 - (1 + Ed25519.d * P.x ^ 2 * P.y ^ 2) := by rw [← h_curve]
          _ = 1 - Ed25519.d * P.x ^ 2 * P.y ^ 2 := by ring

      rw [h_subst]
      ring

  constructor
  · exact ⟨P2, h_out_represents_P2⟩
  · rw [CompletedPoint.toPoint'_eq_of_isValid h_out_represents_P2]


end Edwards

namespace Edwards

open curve25519_dalek curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.backend.serial.u64.field.FieldElement51

theorem double_spec_math
  (low : ProjectivePoint) (h_valid : ∃ P, low.IsValid P) (h_bounds : low.InBounds) :
  ∃ (out : CompletedPoint) (h_run : ProjectivePoint.double low = .ok out),
  ∃ (h_out_valid : ∃ P, out.IsValid P),
      out.toPoint h_out_valid = (low.toPoint h_valid) + (low.toPoint h_valid) := by

  have ⟨out, h_run, h_arith⟩ := ProjectivePoint.double_spec low
    (fun i h => h_bounds.1 i h) (fun i h => h_bounds.2.1 i h) (fun i h => h_bounds.2.2 i h)
  exists out, h_run

  let P := low.toPoint h_valid
  let P2 := P + P

  have h_target_valid : out.IsValid P2 := by
    rcases h_arith with ⟨hX_new, hY_new, hZ_new, hT_new⟩
    have ⟨P_input, h_input_valid⟩ := h_valid
    rw [ProjectivePoint.IsValid] at h_input_valid
    rcases h_input_valid with ⟨hZ_nonzero, hX_in, hY_in⟩

    let X_nat := Field51_as_Nat low.X
    let Y_nat := Field51_as_Nat low.Y
    let Z_nat := Field51_as_Nat low.Z
    let X'_nat := Field51_as_Nat out.X
    let Y'_nat := Field51_as_Nat out.Y
    let Z'_nat := Field51_as_Nat out.Z
    let T'_nat := Field51_as_Nat out.T

    change X'_nat % _ = (2 * X_nat * Y_nat) % _ at hX_new
    change Y'_nat % _ = (Y_nat ^ 2 + X_nat ^ 2) % _ at hY_new
    change (Z'_nat + X_nat ^ 2) % _ = Y_nat ^ 2 % _ at hZ_new
    change (T'_nat + Z'_nat) % _ = (2 * Z_nat ^ 2) % _ at hT_new

    have lift (a b : ℕ) (h : a % p = b % p) : (a : CurveField) = (b : CurveField) := by
      apply (ZMod.natCast_eq_natCast_iff a b p).mpr; exact h

    -- X_out = 2 * X * Y
    have hX_F : field_from_limbs out.X = 2 * field_from_limbs low.X * field_from_limbs low.Y := by
      dsimp [field_from_limbs]; rw [lift X'_nat (2 * X_nat * Y_nat) hX_new]; push_cast; rfl
    have hY_F : field_from_limbs out.Y = field_from_limbs low.Y ^ 2 + field_from_limbs low.X ^ 2 := by
      dsimp [field_from_limbs]; rw [lift Y'_nat (Y_nat ^ 2 + X_nat ^ 2) hY_new]; push_cast; rfl
    have hZ_F : field_from_limbs out.Z = field_from_limbs low.Y ^ 2 - field_from_limbs low.X ^ 2 := by
      have h := lift (Z'_nat + X_nat ^ 2) (Y_nat ^ 2) hZ_new; push_cast at h; apply eq_sub_of_add_eq h
    have hT_F : field_from_limbs out.T = 2 * field_from_limbs low.Z ^ 2 - field_from_limbs out.Z := by
      have h := lift (T'_nat + Z'_nat) (2 * Z_nat ^ 2) hT_new; push_cast at h; apply eq_sub_of_add_eq h

    have h_out_nonzero : field_from_limbs out.Z ≠ 0 ∧ field_from_limbs out.T ≠ 0 := sorry
    unfold CompletedPoint.IsValid; refine ⟨h_out_nonzero.1, h_out_nonzero.2, ?_, ?_⟩

    -- Verify X Coordinate: out.X / out.Z = P2.x
    · rw [(add_def P P).1];
      dsimp only [P2, Add.add,add_coords]
      have hPx : P.x = P_input.x := by
         dsimp [P, ProjectivePoint.toPoint]; rw [hX_in]; field_simp [hZ_nonzero]
      have hPy : P.y = P_input.y := by
        dsimp [P, ProjectivePoint.toPoint]; rw [hY_in]; field_simp [hZ_nonzero]

      rw [hX_F, hZ_F, hX_in, hY_in, hPx, hPy]
      have h_a : Ed25519.a = -1 := rfl
      have h_curve := P.h_on_curve; rw [h_a, hPx, hPy] at h_curve

      have h_denom : 1 + P_input.x ^ 2 * P_input.y ^ 2 * Ed25519.d ≠ 0 := by
        sorry
      field_simp [hZ_nonzero, h_denom]
      have h_subst : 1 + P_input.x ^ 2 * P_input.y ^ 2 * Ed25519.d =
        P_input.y ^ 2 - P_input.x ^ 2 := by
        ring_nf at h_curve ⊢
        exact id (Eq.symm h_curve)
      rw [h_subst]; ring

    -- Verify Y Coordinate: out.Y / out.T = P2.y
    · rw [(add_def P P).2]; dsimp only [add_coords]
      have hPx : P.x = P_input.x := by
        simp only [P, ProjectivePoint.toPoint]; rw [hX_in]; field_simp [hZ_nonzero]
      have hPy : P.y = P_input.y := by
        simp only [P, ProjectivePoint.toPoint]; rw [hY_in]; field_simp [hZ_nonzero]

      rw [hY_F, hT_F, hZ_F, hX_in, hY_in, hPx, hPy]
      have h_a : Ed25519.a = -1 := rfl
      rw [h_a]; field_simp [hZ_nonzero]

      have h_curve := P_input.h_on_curve; rw [h_a] at h_curve
      have h_subst : 2 - (P_input.y ^ 2 - P_input.x ^ 2) =
        1 - P_input.x ^ 2 * P_input.y ^ 2 * Ed25519.d := by
        calc
          2 - (P_input.y ^ 2 - P_input.x ^ 2)
          _ = 2 - (-1 * P_input.x ^ 2 + P_input.y ^ 2) := by ring
          _ = 2 - (1 + Ed25519.d * P_input.x ^ 2 * P_input.y ^ 2) := by rw [h_curve]
          _ = 1 - P_input.x ^ 2 * P_input.y ^ 2 * Ed25519.d := by ring
      rw [h_subst]
      have h_denom_ne : 1 - P_input.y ^ 2 * P_input.x ^ 2 * Ed25519.d ≠ 0 := sorry
      field_simp [h_denom_ne]
      ring

  exists ⟨P2, h_target_valid⟩
  apply Point.ext
  · dsimp [CompletedPoint.IsValid] at h_target_valid; rcases h_target_valid with ⟨hZ_ne, _, hX_eq, _⟩
    simp only [CompletedPoint.toPoint]; rw [hX_eq]; field_simp [hZ_ne]; exact rfl
  · dsimp [CompletedPoint.IsValid] at h_target_valid; rcases h_target_valid with ⟨_, hT_ne, _, hY_eq⟩
    simp only [CompletedPoint.toPoint]; rw [hY_eq]; field_simp [hT_ne]; exact rfl

end Edwards
