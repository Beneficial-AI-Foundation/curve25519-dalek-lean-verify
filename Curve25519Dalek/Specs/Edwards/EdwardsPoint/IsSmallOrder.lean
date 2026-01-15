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

/-! # Spec Theorem for `EdwardsPoint::is_small_order`

Specification and proof for `EdwardsPoint::is_small_order`.

This function determines if an Edwards point is of small order (i.e., if it is in E[8]).

**Source**: curve25519-dalek/src/edwards.rs

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
theorem is_small_order_spec (self : EdwardsPoint) (hself : self.IsValid) :
    ∃ result : Bool, is_small_order self = ok result ∧
    (result ↔ 8 • self.toPoint = 0) := by
    unfold is_small_order
    -- Step 1: Apply mul_by_cofactor_spec to get that multiplying by 8 succeeds
    obtain ⟨ep, hmul, hep_valid, hep_eq⟩ := mul_by_cofactor_spec self hself
    progress*
    -- The proof proceeds as follows:
    -- 1. is_small_order computes ep = mul_by_cofactor(self), which represents 8•self
    -- 2. It then checks if ep equals the identity element using ct_eq
    -- 3. This is equivalent to checking if 8•self.toPoint = 0 (the group identity)
    --
    -- To complete this proof, we need:
    -- - A lemma showing that the identity element's toPoint equals 0
    -- - The ct_eq_spec to connect constant-time equality to mathematical equality
    -- - Lemmas about how toPoint behaves with respect to the group operation
    --
    -- These intermediate lemmas are not yet proven in the codebase, so we
    -- admit this theorem for now.
    sorry


end curve25519_dalek.edwards.EdwardsPoint
