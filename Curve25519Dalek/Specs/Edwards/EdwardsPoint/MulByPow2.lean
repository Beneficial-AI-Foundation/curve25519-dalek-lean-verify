/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation

/-! # Spec Theorem for `EdwardsPoint::mul_by_pow_2`

Specification and proof for `EdwardsPoint::mul_by_pow_2`.

This function computes [2^k]e (the Edwards point e doubled k times for some natural k > 0)
by successive doublings.

**Source**: curve25519-dalek/src/edwards.rs:1328-1340

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Takes an EdwardsPoint e and a positive integer k, and returns the result of doubling the point
k times (i.e., computes [2^k]e where e is the input point)

natural language specs:

• For k = 1, returns double(e)
• For k > 1, satisfies the recursive property: mul_by_pow_2(e, k) = double(mul_by_pow_2(e, k-1))
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.mul_by_pow_2`**:
- For k = 1, returns the doubled point 2e for the input point e
- For k > 1, returns a point equal to double(mul_by_pow_2(e, k-1))
-/
theorem mul_by_pow_2_spec (self : EdwardsPoint) (k : U32) (hself : self.IsValid) (hk : k.val > 0) :
    ∃ result : EdwardsPoint, mul_by_pow_2 self k = ok result ∧
    result.IsValid ∧
    result.toPoint = (2 ^ k.val) • self.toPoint := by
  sorry

end curve25519_dalek.edwards.EdwardsPoint
