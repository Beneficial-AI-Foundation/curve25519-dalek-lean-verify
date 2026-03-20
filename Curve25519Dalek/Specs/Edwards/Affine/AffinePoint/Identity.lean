/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE


/-! # identity

Specification and proof for `AffinePoint::identity`.

This function returns the identity element.

**Source**: curve25519-dalek/src/edwards/affine.rs:L39-L44
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek
open backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.edwards.affine.AffinePoint.Insts.Curve25519_dalekTraitsIdentity

/-
natural language description:

• Returns the identity element of the Edwards curve in affine coordinates (x, y)

natural language specs:

• The function always succeeds (no panic)
• The resulting AffinePoint is the identity element with coordinates (x=0, y=1)
-/

/-- **Spec and proof concerning `edwards.affine.AffinePoint.Insts.Curve25519_dalekTraitsIdentity.identity`**:
- No panic (always returns successfully)
- The resulting AffinePoint is the identity element with coordinates (x=0, y=1)
-/
@[progress]
theorem identity_spec :
    identity ⦃ (q : AffinePoint) =>
      Field51_as_Nat q.x = 0 ∧ Field51_as_Nat q.y = 1 ∧
      q.IsValid ⦄ := by
  unfold identity ZERO ONE
  progress*
  simp only [*]
  decide

end curve25519_dalek.edwards.affine.AffinePoint.Insts.Curve25519_dalekTraitsIdentity
