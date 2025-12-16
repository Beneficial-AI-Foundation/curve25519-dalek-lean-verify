/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByPow2

/-! # Spec Theorem for `EdwardsPoint::mul_by_cofactor`

Specification and proof for `EdwardsPoint::mul_by_cofactor`.

This function computes 8*e (the Edwards point e multiplied by the cofactor 8)
by calling mul_by_pow_2 with k=3 (since 2^3 = 8).

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
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
theorem mul_by_cofactor_spec (e : EdwardsPoint) :
    ∃ e_result,
    mul_by_cofactor e = ok e_result ∧
    ok e_result = mul_by_pow_2 e 3#u32 := by
    -- TO DO: this line needs to be adjusted, we can't have another `ok` in the spec statement
    -- this should use the mathematical notion of edwards curve and multiplication by 8
  obtain ⟨e_result, h', _⟩ := mul_by_pow_2_spec e 3#u32 (by decide)
  use e_result
  constructor
  · exact h'
  · exact h'.symm

end curve25519_dalek.edwards.EdwardsPoint
