/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByPow2
import Curve25519Dalek.Math.Edwards.Representation

/-! # Spec Theorem for `EdwardsPoint::mul_by_cofactor`

Specification and proof for `EdwardsPoint::mul_by_cofactor`.

This function computes 8*e (the Edwards point e multiplied by the cofactor 8)
by calling mul_by_pow_2 with k=3 (since 2^3 = 8).

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Takes an EdwardsPoint e and returns the result of multiplying the point by the cofactor 8 = 2 ^ 3
(i.e., computes [8]e where e is the input point)

natural language specs:

• The function always succeeds (no panic)
• Returns an EdwardsPoint that represents 8e = (2 ^ 3) * e
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.mul_by_cofactor`**:
- No panic (always returns successfully)
- Returns an EdwardsPoint that represents 8e = (2 ^ 3) * e
-/
@[progress]
theorem mul_by_cofactor_spec (self : EdwardsPoint) (hself : self.IsValid) :
    spec (mul_by_cofactor self) (fun result =>
    result.IsValid ∧
    result.toPoint = h • self.toPoint) := by
  /- OLD PROOF
  unfold mul_by_cofactor
  obtain := mul_by_pow_2_spec self 3#u32 hself (by scalar_tac)
  progress*
  constructor
  · assumption
  · simp_all [h]
  -/
  sorry

end curve25519_dalek.edwards.EdwardsPoint
