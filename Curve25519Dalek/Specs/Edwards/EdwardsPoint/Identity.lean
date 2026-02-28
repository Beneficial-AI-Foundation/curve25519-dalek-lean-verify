/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE


/-! # identity

Specification and proof for `EdwardsPoint::identity`.

This function returns the identity element.

**Source**: curve25519-dalek/src/edwards.rs:L409-L416
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek
open backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity

/-
natural language description:

• Returns the identity element of the Edwards curve in extended twisted Edwards coordinates (X, Y, Z, T)

natural language specs:

• The function always succeeds (no panic)
• The resulting EdwardsPoint is the identity element with coordinates (X=0, Y=1, Z=1, T=0)
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity.identity`**:
- No panic (always returns successfully)
- The resulting EdwardsPoint is the identity element with coordinates (X=0, Y=1, Z=1, T=0)
-/
@[progress]
theorem identity_spec :
    identity ⦃ (q : EdwardsPoint) =>
      Field51_as_Nat q.X = 0 ∧ Field51_as_Nat q.Y = 1 ∧
      Field51_as_Nat q.Z = 1 ∧ Field51_as_Nat q.T = 0 ⦄ := by
  unfold identity
  progress*

end curve25519_dalek.edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity
