/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Mul

/-! # Spec Theorems for `RistrettoPoint::mul`

Specifications and proofs for scalar multiplication of Ristretto points.

Two trait implementations are covered here:

- `Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint.mul`:
  `&RistrettoPoint * &Scalar → RistrettoPoint`, delegating to `edwards.EdwardsPoint.Insts.CoreOpsArithMulSharedBScalarEdwardsPoint.mul`.

- `Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint.mul` — the commutative variant:
  `&Scalar * &RistrettoPoint → RistrettoPoint`, independently delegating to `SharedAScalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul`.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.ristretto
namespace curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint

/-
natural language description:

• Takes a valid Ristretto point (self : RistrettoPoint) and a canonical scalar (scalar : scalar.Scalar)
• Returns the scalar multiple [scalar]self, i.e., the point added to itself scalar times
• Delegates to edwards.EdwardsPoint.Insts.CoreOpsArithMulSharedBScalarEdwardsPoint.mul since RistrettoPoint
  is represented as an underlying EdwardsPoint

natural language specs:

• The function always succeeds (no panic) for valid input RistrettoPoints r and canonical Scalars s
• The result is a valid RistrettoPoint
• The result = r + ... + r represents the input RistrettoPoint r added to itself s-times
-/

/-- **Spec and proof concerning `Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint.mul`**:
• The function always succeeds (no panic) for valid input RistrettoPoints r and canonical Scalars s
• The result is a valid RistrettoPoint
• The result = r + ... + r represents the input RistrettoPoint r added to itself s-times
-/
@[progress]
theorem mul_spec (r : RistrettoPoint) (s : scalar.Scalar)
    (h_s_canonical : U8x32_as_Nat s.bytes < L)
    (h_rist_valid : r.IsValid) :
    mul r s ⦃ result =>
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • r.toPoint ⦄ := by
  unfold mul edwards.EdwardsPoint.Insts.CoreOpsArithMulSharedBScalarEdwardsPoint.mul
  progress*
  · exact h_rist_valid.1
  · constructor
    · unfold RistrettoPoint.IsValid
      refine ⟨ep_post_1, ?_⟩
      rw [EdwardsPoint_IsSquare_iff_IsEven ep ep_post_1, ep_post_2]
      obtain ⟨Q, hQ⟩ := (IsEven_iff_in_doubling_image _).mp ((EdwardsPoint_IsSquare_iff_IsEven r h_rist_valid.1).mp h_rist_valid.2)
      exact (IsEven_iff_in_doubling_image _).mpr ⟨U8x32_as_Nat s.bytes • Q, by rw [hQ, nsmul_add]⟩
    · simp only [RistrettoPoint.toPoint]
      exact ep_post_2

/-
Note:

One RistrettoPoint r corresponds to an equivalence class of several
mathematical curve points.

The command r.toPoint thus maps r to one of these concrete representatives on the curve (to the representative
that currently just so happens to represent r).

The equation

result.toPoint = (U8x32_as_Nat s.bytes) • r.toPoint

thus assures that the concrete representative of the input RistrettoPoints r on the curve sums up to
the concrete representative of the output Ristretto point on the curve if mathematically added to itself s times.
Since the addition on RistrettoPoints is mathematically well-defined (i.e., it does not depend on the choice of representatives), the condition

result.toPoint = (U8x32_as_Nat s.bytes) • r.toPoint

thus indeed implies that the output RistrettoPoint (seen as an equivalence class) is the mathematically correct sum
of r + ... + r (s-times), even though we are only working at the level of (fairly arbitrary) representatives.

The fact that the addition of RistrettoPoints is indeed well-defined and does not depend on the chosen
representatives follows from standard results in abstract algebra: in any set of left cosets G/N, the product

(aN)(bN)=(ab)N

constitutes a well-defined operation that does not depend on the chosen representatives a, b iff N is a normal subgroup;
and in an Abelian group (our elliptic curve group is Abelian), every subgroup is normal.
-/

end curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint

namespace curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint

/-
natural language description:

• Takes a canonical scalar (self : Scalar) and a valid Ristretto point (point : RistrettoPoint)
• Returns the scalar multiple [self]point, i.e., the point added to itself self times
• This is the commutative variant (Scalar * Point rather than Point * Scalar);
  it independently delegates to SharedAScalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul

natural language specs:

• The function always succeeds (no panic) for canonical input Scalars s and valid input RistrettoPoints r
• The result is a valid RistrettoPoint
• The result = r + ... + r represents the input RistrettoPoint r added to itself s-times
-/

/-- **Spec and proof concerning `Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint.mul`**:
• The function always succeeds (no panic) for canonical input Scalars s and valid input RistrettoPoints r
• The result is a valid RistrettoPoint
• The result = r + ... + r represents the input RistrettoPoint r added to itself s-times
-/
@[progress]
theorem mul_spec (s : scalar.Scalar) (r : RistrettoPoint)
    (h_s_canonical : U8x32_as_Nat s.bytes < L)
    (h_rist_valid : r.IsValid) :
    mul s r ⦃ result =>
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • r.toPoint ⦄ := by
  exact Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint.mul_spec r s h_s_canonical h_rist_valid

end curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint
