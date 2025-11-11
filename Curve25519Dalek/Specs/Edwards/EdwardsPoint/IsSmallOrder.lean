/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `EdwardsPoint::is_small_order`

Specification and proof for `EdwardsPoint::is_small_order`.

This function determines if an Edwards point is of small order (i.e., if it is in E[8]).

**Source**: curve25519-dalek/src/edwards.rs:L1365-L1367

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Determines whether an EdwardsPoint is in the torsion subgroup E[8]

• A point has small order if multiplying it by the cofactor (= 8) results in the identity element

natural language specs:

• The function always succeeds (no panic)
• Returns `true` if and only if the point is in the torsion subgroup E[8]
• Equivalently, returns `true` iff multiplying by the cofactor yields the identity element
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.is_small_order`**:
- No panic (always returns successfully)
- Returns `true` if and only if the point has small order (is in the torsion subgroup E[8])
- This is determined by checking if multiplying by the cofactor yields the identity element
-/
@[progress]
theorem is_small_order_spec (e : EdwardsPoint) :
    ∃ b e8 id eq_choice,
    is_small_order e = ok b ∧
    mul_by_cofactor e = ok e8 ∧
    Identitycurve25519_dalekedwardsEdwardsPoint.identity = ok id ∧
    ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint.ct_eq e8 id = ok eq_choice ∧
    (b = true ↔ eq_choice = Choice.one) := by
    sorry

end curve25519_dalek.edwards.EdwardsPoint
