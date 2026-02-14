/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Montgomery.Representation

/-! # Spec Theorem for `differential_add_and_double`

Specification and proof for
`curve25519_dalek::montgomery::differential_add_and_double`.

This function performs simultaneous differential addition and point doubling
on Montgomery curve points in projective coordinates, which is the core operation
of the Montgomery ladder scalar multiplication algorithm.

**Source**: curve25519-dalek/src/montgomery.rs, lines 351:0-389:1

## Mathematical Background

Given Montgomery projective points P = (U_P : W_P) and Q = (U_Q : W_Q),
and the affine x-coordinate of their difference P - Q, this function computes:
- 2P (point doubling)
- P + Q (differential addition)

The Montgomery ladder uses this operation because knowing the difference
allows efficient addition without needing the full coordinates of both points.

## Formulas

For point doubling [2]P:
- U_{2P} = (U_P^2 - W_P^2)^2
- W_{2P} = 4U_P W_P ((U_P - W_P)^2 + ((A+2)/4) · 4U_P W_P)

For differential addition P + Q (given x(P - Q)):
- U_{P+Q} = 4(U_P U_Q - W_P W_Q)^2
- W_{P+Q} = x(P-Q) · 4(U_P W_Q - W_P U_Q)^2

-/

open Aeneas.Std Result
open Montgomery
namespace curve25519_dalek.montgomery

/-! ## Projective to Affine Conversion -/

/-- A projective point (U : W) with W ≠ 0 represents the affine u-coordinate U/W.
    This predicate establishes the relationship between a projective representation
    and the corresponding affine Montgomery point.

    Montgomery curve operations use projective coordinates (U : W) to avoid field inversions
    during intermediate computations. The projective representation is homogeneous:
    (U : W) and (λU : λW) represent the same affine point for any non-zero λ. -/
def ProjectivePoint.representsAffine (proj : ProjectivePoint) (affine_u : CurveField) : Prop :=
  proj.W.toField ≠ 0 ∧
  affine_u = proj.U.toField / proj.W.toField

/-- A projective point represents a Montgomery curve point if the affine u-coordinate
    corresponds to a valid point on the curve.

    This connects the Rust implementation's `ProjectivePoint` type (with U, W coordinates)
    to the mathematical `Point` type (representing points on the Montgomery curve).
    The v-coordinate is not stored in projective representation as it's not needed
    for the Montgomery ladder scalar multiplication algorithm. -/
def ProjectivePoint.representsPoint (proj : ProjectivePoint) (P : Point) : Prop :=
  ∃ affine_u : CurveField,
    proj.representsAffine affine_u ∧
    get_u P = affine_u

/-
Natural language description:

• Takes two Montgomery projective points P and Q
• Takes the affine x-coordinate of P - Q (the difference)
• Computes both:
  - The doubled point [2]P
  - The sum point P + Q
• Returns both results as projective points

The function is constant-time and uses the Montgomery ladder formulas
which are optimized for scalar multiplication.

Natural language specs:

• The function always succeeds (no panic)
• Returns a pair (P', Q') where:
  - P' = [2]P (point doubling of P)
  - Q' = P + Q (differential addition)
• The computation is constant-time to prevent timing attacks
• Uses optimized field arithmetic with limb reduction
-/

/-- **Spec and proof concerning `montgomery.differential_add_and_double`**:
- The function always succeeds (no panic conditions)
- Returns two projective points representing [2]P and P + Q
- Mathematical correctness: the output points correspond to the correct
  Montgomery curve operations in the projective coordinate system
- Preserves the relationship: if affine_PmQ is the x-coordinate of P - Q,
  then the returned points satisfy the Montgomery ladder invariants
-/
@[progress]
theorem differential_add_and_double_spec
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51)
    (hP_U : ∀ i < 5, P.U[i]!.val < 2 ^ 54)
    (hP_W : ∀ i < 5, P.W[i]!.val < 2 ^ 54)
    (hQ_U : ∀ i < 5, Q.U[i]!.val < 2 ^ 54)
    (hQ_W : ∀ i < 5, Q.W[i]!.val < 2 ^ 54)
    (h_affine : ∀ i < 5, affine_PmQ[i]!.val < 2 ^ 54)
    -- Mathematical preconditions
    (MP : Point) (MQ : Point)
    (hP_rep : P.representsPoint MP)
    (hQ_rep : Q.representsPoint MQ)
    (hPmQ : affine_PmQ.toField = get_u (MP - MQ)) :
    ∃ result,
    differential_add_and_double P Q affine_PmQ = ok result ∧
    (let (P_doubled, P_plus_Q) := result
     -- Both satisfy field bounds
     (∀ i < 5, P_doubled.U[i]!.val < 2 ^ 54) ∧
     (∀ i < 5, P_doubled.W[i]!.val < 2 ^ 54) ∧
     (∀ i < 5, P_plus_Q.U[i]!.val < 2 ^ 54) ∧
     (∀ i < 5, P_plus_Q.W[i]!.val < 2 ^ 54) ∧
     -- Mathematical correctness:
     -- P_doubled represents [2]P (point doubling)
     P_doubled.representsPoint (2 • MP) ∧
     -- P_plus_Q represents P + Q (differential addition)
     P_plus_Q.representsPoint (MP + MQ)) := by
  unfold differential_add_and_double
  progress*

  /- Proof sketch:

  At this point, progress* has handled the monadic composition of all the field operations.
  We now need to prove:
  1. All field bounds (∀ i < 5, result.1.U[i]!.val < 2^54) for both output projective points
  2. Mathematical correctness: result.1.representsPoint (2 • MP)
  3. Mathematical correctness: result.2.representsPoint (MP + MQ)

  Strategy:

  ## Part 1: Field Bounds
  The computation sequence is:
    t0 = P.U + P.W        (add: < 2^54 if inputs < 2^53)
    t1 = P.U - P.W        (sub: bounded)
    t2 = Q.U + Q.W        (add: < 2^54 if inputs < 2^53)
    t3 = Q.U - Q.W        (sub: bounded)
    t4 = t0.square        (square_spec: < 2^52)
    t5 = t1.square        (square_spec: < 2^52)
    t6 = t4 - t5          (sub: bounded)
    t7 = t0 * t3          (mul_spec: < 2^52)
    t8 = t1 * t2          (mul_spec: < 2^52)
    t9 = t7 + t8          (add: bounded)
    t10 = t7 - t8         (sub: bounded)
    t11 = t9.square       (square_spec: < 2^52)
    t12 = t10.square      (square_spec: < 2^52)
    t13 = A+2/4 * t6      (mul_spec: < 2^52)
    t14 = t4 * t5         (mul_spec: < 2^52, output is P_doubled.U)
    t15 = t13 + t5        (add: bounded)
    t16 = t6 * t15        (mul_spec: < 2^52, output is P_doubled.W)
    t17 = affine_PmQ * t12 (mul_spec: < 2^52, output is P_plus_Q.W)

  Result:
    - P_doubled = (t14, t16) where both have limbs < 2^52 < 2^54 ✓
    - P_plus_Q = (t11, t17) where both have limbs < 2^52 < 2^54 ✓

  ## Part 2: Mathematical Correctness for Point Doubling
  Need to show: ({ U := t14, W := t16 }).representsPoint (2 • MP)

  By definition of representsPoint, need to show:
    ∃ affine_u,
      t16.toField ≠ 0 ∧
      affine_u = t14.toField / t16.toField ∧
      get_u (2 • MP) = affine_u

  This requires:
    - Expanding the Montgomery doubling formula
    - Using the field arithmetic properties from mul_spec, square_spec, etc.
    - Showing that t14/t16 = U_{2P}/W_{2P} as per Montgomery doubling formula

  ## Part 3: Mathematical Correctness for Differential Addition
  Need to show: ({ U := t11, W := t17 }).representsPoint (MP + MQ)

  By definition of representsPoint, need to show:
    ∃ affine_u,
      t17.toField ≠ 0 ∧
      affine_u = t11.toField / t17.toField ∧
      get_u (MP + MQ) = affine_u

  This requires:
    - Using the differential addition formula
    - Using the precondition hPmQ that affine_PmQ.toField = get_u (MP - MQ)
    - Showing that t11/t17 equals the differential addition formula output

  Key lemmas needed:
    - Relationship between Field51_as_Nat and toField
    - Properties of toField under arithmetic operations
    - Montgomery curve point addition and doubling formulas in affine coordinates
    - Connection between projective formulas and affine results
  -/

  sorry -- Complete field bounds and mathematical correctness proof

end curve25519_dalek.montgomery
