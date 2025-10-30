/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `EdwardsPoint::as_projective`

Specification and proof for `EdwardsPoint::as_projective`.

This function converts to projective coordinates.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to projective coordinates (X, Y, Z)

natural language specs:

• The function always succeeds (no panic)
• The resulting ProjectivePoint has the same X, Y, Z coordinates as the input EdwardsPoint
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.as_projective`**:
- No panic (always returns successfully)
- The resulting ProjectivePoint coordinates match the EdwardsPoint coordinates (X, Y, Z)
-/
theorem as_projective_spec (e : EdwardsPoint) :
∃ q, edwards.EdwardsPoint.as_projective e = ok q ∧
q.X = e.X ∧ q.Y = e.Y ∧ q.Z = e.Z := by
unfold edwards.EdwardsPoint.as_projective
simp

end curve25519_dalek.edwards.EdwardsPoint
