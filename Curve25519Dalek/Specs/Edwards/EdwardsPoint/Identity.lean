/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs


/-! # identity

Specification and proof for `EdwardsPoint::identity`.

This function returns the identity element.

**Source**: curve25519-dalek/src/edwards.rs:L409-L416
-/

open Aeneas.Std Result curve25519_dalek
open backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.edwards.Identitycurve25519_dalekedwardsEdwardsPoint

/-
natural language description:

• Returns the identity element of the Edwards curve in extended twisted Edwards coordinates (X, Y, Z, T)

natural language specs:

• The function always succeeds (no panic)
• The resulting EdwardsPoint is the identity element with coordinates (X=0, Y=1, Z=1, T=0)
-/

/-- **Spec and proof concerning `edwards.Identitycurve25519_dalekedwardsEdwardsPoint.identity`**:
- No panic (always returns successfully)
- The resulting EdwardsPoint is the identity element with coordinates (X=0, Y=1, Z=1, T=0)
-/
@[progress]
theorem identity_spec :
  ∃ q, identity = ok q ∧
  q.X = ZERO ∧ q.Y = ONE ∧ q.Z = ONE ∧ q.T = ZERO := by
  unfold identity
  simp

end curve25519_dalek.edwards.Identitycurve25519_dalekedwardsEdwardsPoint
