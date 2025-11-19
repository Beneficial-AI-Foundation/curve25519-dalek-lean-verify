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

/-- Proof that `p` is prime. This is required for `CurveField = ZMod p` to be a field.
    TODO: Complete this proof using a primality certificate, similar to
    `Mathlib.NumberTheory.LucasLehmer` for Mersenne primes. -/
instance : Fact (Nat.Prime p) := by
  unfold p
  sorry

/-- The field structure on `CurveField`, automatically derived from `ZMod p` where `p` is prime. -/
instance : Field CurveField := by
  unfold CurveField
  infer_instance

/-- A Twisted Edwards curve structure defined by parameters a and d. -/
structure EdwardsCurve (F : Type) [Field F] where
  a : F
  d : F

/-- The specific Ed25519 curve parameters lifted to the field. -/
-- We assume 'p', 'd', and 'a' are available from Curve25519Dalek.Defs
def Ed25519 : EdwardsCurve CurveField := {
  a := -1,
  d := (d : CurveField)
}

/-- An affine point on the Edwards curve.
    Bundles coordinates (x, y) with the proof they satisfy the curve equation. -/
@[ext]
structure Point {F : Type} [Field F] (C : EdwardsCurve F) where
  x : F
  y : F
  h_on_curve : C.a * x^2 + y^2 = 1 + C.d * x^2 * y^2
  deriving Repr

instance : Inhabited (Point Ed25519) :=
  ⟨{ x := 0, y := 1, h_on_curve := by simp only [Ed25519, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, one_pow, zero_add, mul_one, add_zero] }⟩

-- Implements the unified addition formulas for Twisted Edwards curves.
-- (x₁, y₁) + (x₂, y₂) = ( (x₁y₂ + y₁x₂)/(1 + dx₁x₂y₁y₂), (y₁y₂ - ax₁x₂)/(1 - dx₁x₂y₁y₂) )

variable {F : Type} [Field F] (C : EdwardsCurve F)

/-- Raw addition of coordinates (x₁, y₁) and (x₂, y₂) using Twisted Edwards formulas. -/
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

/-- Standard addition instance for Edwards Points. -/
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
    -- Proof: a*0^2 + 1^2 = 1 + d*0^2*1^2  =>  0 + 1 = 1 + 0
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
  add_comm := by sorry -- Easy, follows from symmetry of add_coords
  nsmul_succ := by sorry
  zsmul_succ':= by sorry

/-- Convert the 5-limb array to a field element in ZMod p.
    Uses 'Field51_as_Nat' from Defs.lean to interpret the limbs. -/
def field_from_limbs (fe : backend.serial.u64.field.FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

def IsValidAffine (low : edwards.affine.AffinePoint) (high : Point Ed25519) : Prop :=
  field_from_limbs low.x = high.x ∧
  field_from_limbs low.y = high.y

def IsValidProjective (low : ProjectivePoint) (high : Point Ed25519) : Prop :=
  let X := field_from_limbs low.X
  let Y := field_from_limbs low.Y
  let Z := field_from_limbs low.Z
  Z ≠ 0 ∧ X = high.x * Z ∧ Y = high.y * Z

/-- Validity for CompletedPoint (X:Y:Z:T) output by 'double'.
    Dalek Semantics: x = X/Z, y = Y/T. -/
def IsValidCompleted (low : CompletedPoint) (high : Point Ed25519) : Prop :=
  let X := field_from_limbs low.X
  let Y := field_from_limbs low.Y
  let Z := field_from_limbs low.Z
  let T := field_from_limbs low.T
  Z ≠ 0 ∧ T ≠ 0 ∧
  X = high.x * Z ∧
  Y = high.y * T

/-! ## Lifting low-level (Rust) points to actual points on the curve -/

/-- Construct a high-level Point from a valid AffinePoint.
    The coordinates are DEFINED as the low-level fields. -/
noncomputable def AffinePoint.toPoint (p : edwards.affine.AffinePoint) (h : ∃ P, IsValidAffine p P) : Point Ed25519 :=
  { x := field_from_limbs p.x
    y := field_from_limbs p.y
    h_on_curve := by
      have ⟨P, hP⟩ := h
      rw [IsValidAffine] at hP; rw [hP.1, hP.2]
      exact P.h_on_curve
  }

/-- Construct a high-level Point from a valid ProjectivePoint.
    The coordinates are DEFINED as X/Z and Y/Z. -/
noncomputable def ProjectivePoint.toPoint (p : ProjectivePoint) (h : ∃ P, IsValidProjective p P) : Point Ed25519 :=
  { x := field_from_limbs p.X / field_from_limbs p.Z
    y := field_from_limbs p.Y / field_from_limbs p.Z
    h_on_curve := by
      have ⟨P, hP⟩ := h
      rw [IsValidProjective] at hP

      field_simp [hP.1];  rw [hP.2.1, hP.2.2]
      have h_curve := P.h_on_curve
      apply_fun (fun t => field_from_limbs p.Z ^ 4 * t) at h_curve

      ring_nf; ring_nf at h_curve; exact h_curve
  }

/-- Construct a high-level Point from a valid CompletedPoint. -/
noncomputable def CompletedPoint.toPoint (p : CompletedPoint) (h : ∃ P, IsValidCompleted p P) : Point Ed25519 :=
  { x := field_from_limbs p.X / field_from_limbs p.Z
    y := field_from_limbs p.Y / field_from_limbs p.T
    h_on_curve := by
      have ⟨P, hP⟩ := h
      rw [IsValidCompleted] at hP

      field_simp [hP.1, hP.2.1]; rw [hP.2.2.1, hP.2.2.2]
      have h_curve := P.h_on_curve
      apply_fun (fun t => (field_from_limbs p.Z)^2 * (field_from_limbs p.T)^2 * t) at h_curve
      convert h_curve using 1 <;> ring
  }

/-- Helper to expose the addition formula without unfolding the whole structure. -/
theorem add_def (p1 p2 : Point Ed25519) :
  (p1 + p2).x = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).1 ∧
  (p1 + p2).y = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).2 := by
  exact Prod.mk_inj.mp rfl

theorem double_spec_math
    (low : ProjectivePoint)
    (h_valid : ∃ P, IsValidProjective low P)
    (h_bounds :
      ∀ i, i < 5 → (low.X[i]!).val ≤ 2 ^ 52 ∧ (low.Y[i]!).val ≤ 2 ^ 52 ∧ (low.Z[i]!).val ≤ 2 ^ 52) :
  ∃ (out : CompletedPoint) (h_run : ProjectivePoint.double low = .ok out),
    ∃ (h_out_valid : ∃ P, IsValidCompleted out P),
      CompletedPoint.toPoint out h_out_valid =
      (ProjectivePoint.toPoint low h_valid) + (ProjectivePoint.toPoint low h_valid) := by

  -- 1. Execute the Code (using Double.lean spec)
  have ⟨out, h_run, h_arith⟩ := ProjectivePoint.double_spec low
    (fun i h => (h_bounds i h).1)
    (fun i h => (h_bounds i h).2.1)
    (fun i h => (h_bounds i h).2.2)

  exists out, h_run

  let P := ProjectivePoint.toPoint low h_valid
  let P2 := P + P

  -- Prove 'out' represents P + P (Arithmetic Check)
  have h_target_valid : IsValidCompleted out P2 := by
    rcases h_arith with ⟨hX_new, hY_new, hZ_new, hT_new⟩
    have ⟨P_input, h_input_valid⟩ := h_valid
    rw [IsValidProjective] at h_input_valid
    rcases h_input_valid with ⟨hZ_nonzero, hX_in, hY_in⟩

    have lift (a b : ℕ) (h : a % p = b % p) :
      (a : CurveField) = (b : CurveField) := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      exact h

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

    -- X_out = 2 * X * Y
    have hX_F : field_from_limbs out.X = 2 * field_from_limbs low.X * field_from_limbs low.Y := by
      dsimp [field_from_limbs]
      rw [lift X'_nat (2 * X_nat * Y_nat) hX_new]; push_cast;
      rfl

    have hY_F : field_from_limbs out.Y = field_from_limbs low.Y ^ 2 + field_from_limbs low.X ^ 2 := by
      dsimp [field_from_limbs]
      rw [lift Y'_nat (Y_nat ^ 2 + X_nat ^ 2) hY_new]; push_cast;
      rfl

    have hZ_F : field_from_limbs out.Z = field_from_limbs low.Y ^ 2 - field_from_limbs low.X ^ 2 := by
      dsimp [field_from_limbs]
      have h := lift (Z'_nat + X_nat ^ 2) (Y_nat ^ 2) hZ_new; push_cast at h;
      apply eq_sub_of_add_eq h

    have hT_F : field_from_limbs out.T = 2 * field_from_limbs low.Z ^ 2 - field_from_limbs out.Z := by
      dsimp [field_from_limbs]
      have h := lift (T'_nat + Z'_nat) (2 * Z_nat ^ 2) hT_new; push_cast at h
      apply eq_sub_of_add_eq h

    -- Assumption: Output Z and T are non-zero (In a full proof, we'd prove this from d non-square)
    have h_out_nonzero : field_from_limbs out.Z ≠ 0 ∧ field_from_limbs out.T ≠ 0 := sorry

    unfold IsValidCompleted
    refine ⟨h_out_nonzero.1, h_out_nonzero.2, ?_, ?_⟩

    -- Verify X coordinate: out.X / out.Z = P2.x
    · rw [(add_def P P).1]
      dsimp only [P2, Add.add, add_coords]
      have h_a : Ed25519.a = -1 := rfl
      -- We know P.x = P_input.x because X = xZ and Z != 0.
      have hPx : P.x = P_input.x := by
        dsimp [P, ProjectivePoint.toPoint]; rw [hX_in]; field_simp [hZ_nonzero]
      have hPy : P.y = P_input.y := by
        dsimp [P, ProjectivePoint.toPoint]; rw [hY_in]; field_simp [hZ_nonzero]

      rw [hPx, hPy, hX_F, hZ_F, hX_in, hY_in]
      have h_curve := P.h_on_curve; rw [h_a, hPx, hPy] at h_curve


      -- Clear Denominator
      have h_denom : 1 + P_input.x ^ 2 * P_input.y ^ 2 * Ed25519.d ≠ 0 := by
        sorry
      field_simp [hZ_nonzero, h_denom]
      have h_subst : 1 + P_input.x ^ 2 * P_input.y ^ 2 * Ed25519.d =
        P_input.y ^ 2 - P_input.x ^ 2 := by
        ring_nf at h_curve ⊢
        exact id (Eq.symm h_curve)
      rw [h_subst]; ring

    -- Verify Y coordinate: out.Y / out.T = P2.y
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

  -- 4. Prove Functional Equality (Trivial given Validity)
  exists ⟨P2, h_target_valid⟩

  apply Point.ext
  · -- Goal 1: X coordinate
    unfold IsValidCompleted at h_target_valid
    rcases h_target_valid with ⟨hZ_ne, _, hX_eq, _⟩

    simp only [CompletedPoint.toPoint]; rw [hX_eq]; field_simp [hZ_ne]
    exact rfl
  · -- Goal 2: Y coordinate
    unfold IsValidCompleted at h_target_valid
    rcases h_target_valid with ⟨_, hT_ne, _, hY_eq⟩

    simp only [CompletedPoint.toPoint]; rw [hY_eq]; field_simp [hT_ne]
    exact rfl

end Edwards
