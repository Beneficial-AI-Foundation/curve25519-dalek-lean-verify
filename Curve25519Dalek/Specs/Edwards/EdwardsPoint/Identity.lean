/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang, Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::identity`

Returns the identity element of the Edwards curve in extended twisted Edwards coordinates
(X, Y, Z, T).

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::identity`**
• The function always succeeds (no panic)
• The resulting EdwardsPoint has coordinates (X = 0, Y = 1, Z = 1, T = 0)
• The resulting EdwardsPoint is valid
• The resulting EdwardsPoint represents the identity element of the Ed25519 group
-/
@[step]
theorem identity_spec :
    identity ⦃ (result : EdwardsPoint) =>
      Field51_as_Nat result.X = 0 ∧
      Field51_as_Nat result.Y = 1 ∧
      Field51_as_Nat result.Z = 1 ∧
      Field51_as_Nat result.T = 0 ∧
      result.IsValid ∧
      result.toPoint = 0 ⦄ := by
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
