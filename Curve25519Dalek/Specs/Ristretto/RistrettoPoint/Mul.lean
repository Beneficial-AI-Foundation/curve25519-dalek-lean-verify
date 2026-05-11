/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Mul

/-!
# Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::mul`

Scalar multiplication of a Ristretto point: given a canonical scalar `s` and a valid
`RistrettoPoint` `r`, computes the scalar multiple `[s]r`, i.e., `r` added to itself `s` times.
Since `RistrettoPoint` wraps an underlying `EdwardsPoint`, the computation delegates to the
corresponding Edwards scalar multiplication.

Two trait implementations are covered here:

- `Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint.mul`:
  `&RistrettoPoint * &Scalar → RistrettoPoint`; takes a valid Ristretto point `self` and a
  canonical scalar `scalar`; delegates to
  `edwards.EdwardsPoint.Insts.CoreOpsArithMulSharedBScalarEdwardsPoint.mul`.

- `Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint.mul`:
  `&Scalar * &RistrettoPoint → RistrettoPoint` — the commutative variant; takes a canonical
  scalar `self` and a valid Ristretto point `point`; independently delegates to
  `SharedAScalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul`.

A `RistrettoPoint` `r` represents an equivalence class of several mathematical curve points;
`r.toPoint` selects one concrete representative. The postcondition
`result.toPoint = s • r.toPoint` therefore asserts that the representative of the output equals
`s` times the representative of the input. Since Ristretto point addition is well-defined
independently of the choice of representative — in an Abelian group every subgroup is normal, so
left-coset multiplication `(aN)(bN) = (ab)N` is unambiguous — this implies that the output
`RistrettoPoint` equals the correct scalar multiple `[s]r` as an equivalence class.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.ristretto
namespace curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint

/-- **Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::mul`**
• The function always succeeds (no panic) for valid input RistrettoPoints r and canonical Scalars s
• The result is a valid RistrettoPoint
• The result = r + ... + r represents the input RistrettoPoint r added to itself s-times
-/
@[step]
theorem mul_spec (self : RistrettoPoint) (scalar : scalar.Scalar)
    (hscalar : U8x32_as_Nat scalar.bytes < 2 ^ 255) (hself : self.IsValid) :
    mul self scalar ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat scalar.bytes) • self.toPoint ⦄ := by
  unfold mul edwards.EdwardsPoint.Insts.CoreOpsArithMulSharedBScalarEdwardsPoint.mul
  step*
  · constructor
    · unfold RistrettoPoint.IsValid
      refine ⟨ep_post1, ?_⟩
      rw [EdwardsPoint_IsSquare_iff_IsEven ep ep_post1, ep_post2]
      obtain ⟨Q, hQ⟩ := (IsEven_iff_in_doubling_image _).mp
        ((EdwardsPoint_IsSquare_iff_IsEven self hself.1).mp hself.2)
      exact (IsEven_iff_in_doubling_image _).mpr
        ⟨U8x32_as_Nat scalar.bytes • Q, by grind [nsmul_add]⟩
    · simpa [RistrettoPoint.toPoint]

end curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint

namespace curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::mul`**
• The function always succeeds (no panic) for canonical Scalars s and valid RistrettoPoints r
• The result is a valid RistrettoPoint
• The result = r + ... + r represents the input RistrettoPoint r added to itself s-times
-/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : RistrettoPoint)
    (hself : U8x32_as_Nat self.bytes < 2 ^ 255) (hpoint : point.IsValid) :
    mul self point ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧ result.toPoint = (U8x32_as_Nat self.bytes) • point.toPoint ⦄ := by
  exact Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint.mul_spec
    point self hself hpoint

end curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint
