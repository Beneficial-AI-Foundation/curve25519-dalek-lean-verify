/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang, Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
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

• Returns the identity element of the Edwards curve in extended
  twisted Edwards coordinates (X, Y, Z, T)

natural language specs:

• The function always succeeds (no panic)
• The resulting EdwardsPoint is the identity element with coordinates (X=0, Y=1, Z=1, T=0)
-/

/-- **Spec and proof** concerning:
 `edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity.identity`
- No panic (always returns successfully)
- The resulting EdwardsPoint is the identity element of the Ed25519 group
-/
@[step]
theorem identity_spec :
    identity ⦃ (q : EdwardsPoint) =>
      Field51_as_Nat q.X = 0 ∧ Field51_as_Nat q.Y = 1 ∧
      Field51_as_Nat q.Z = 1 ∧ Field51_as_Nat q.T = 0 ∧
      q.IsValid ∧ q.toPoint = 0 ⦄ := by
  unfold identity ZERO ONE
  step*
  have h0 : Field51_as_Nat fe = 0 := by rw [fe_post2]; decide
  have h1 : Field51_as_Nat fe1 = 1 := by rw [fe1_post2]; decide
  have hv : ({ X := fe, Y := fe1, Z := fe1, T := fe } : EdwardsPoint).IsValid := by
    rw [fe_post1, fe1_post1]; decide
  refine ⟨h0, h1, h1, h0, hv, ?_⟩
  have ⟨hpx, hpy⟩ := EdwardsPoint.toPoint_of_isValid hv
  ext
  · simp [hpx, toField, h0, h1]
  · simp [hpy, toField, h1]

end curve25519_dalek.edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity
