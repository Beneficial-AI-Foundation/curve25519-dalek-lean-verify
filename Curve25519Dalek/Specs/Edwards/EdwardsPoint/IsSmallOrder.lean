/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByCofactor
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.CtEq
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `EdwardsPoint::is_small_order`

Specification and proof for `EdwardsPoint::is_small_order`.

This function determines if an Edwards point is of small order (i.e., if it is in E[8]).

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result Edwards
open curve25519_dalek.backend.serial.u64.field.FieldElement51
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

/-- **Spec for `edwards.EdwardsPoint.is_small_order`**:
- Returns `true` if and only if the point has small order (is in the torsion subgroup E[8])
- This is determined by checking if multiplying by the cofactor yields the identity element
-/
@[progress]
theorem is_small_order_spec (self : EdwardsPoint) (hself : self.IsValid) :
    is_small_order self ⦃ result =>
      (result ↔ h • self.toPoint = 0) ⦄ := by
  sorry

end curve25519_dalek.edwards.EdwardsPoint
