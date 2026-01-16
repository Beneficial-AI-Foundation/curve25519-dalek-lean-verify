/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
/-! # Spec Theorem for `ProjectiveNielsPoint::conditional_assign`

Specification and proof for `ProjectiveNielsPoint::conditional_assign`.

This function conditionally assigns the value of another ProjectiveNielsPoint
to self based on a Choice value. It is a constant-time operation used in
cryptographic implementations to avoid timing side-channels.

Given:
- a ProjectiveNielsPoint `self` with coordinates (Y_plus_X, Y_minus_X, Z, T2d),
- a ProjectiveNielsPoint `other` with coordinates (Y_plus_X', Y_minus_X', Z', T2d'),
- a Choice `choice` (which is either 0 or 1),

it updates `self` such that:
- if choice == 1: self = other (all coordinates are replaced)
- if choice == 0: self remains unchanged

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 305:4-310:5
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
open curve25519_dalek.backend.serial.curve_models
namespace curve25519_dalek.backend.serial.curve_models.ConditionallySelectableProjectiveNielsPoint

/-
natural language description:

• Takes a ProjectiveNielsPoint self = (Y_plus_X, Y_minus_X, Z, T2d) and another
  ProjectiveNielsPoint other = (Y_plus_X', Y_minus_X', Z', T2d'), along with a
  Choice value, and conditionally assigns other to self in constant time.

natural language specs:

• The function always succeeds (no panic)
• Given inputs self = (Y_plus_X, Y_minus_X, Z, T2d), other = (Y_plus_X', Y_minus_X', Z', T2d'),
  and choice, the output self' = (Y_plus_X'', Y_minus_X'', Z'', T2d'') satisfies:
  - If choice represents 1 (true):
    Y_plus_X'' = Y_plus_X', Y_minus_X'' = Y_minus_X', Z'' = Z', T2d'' = T2d'
  - If choice represents 0 (false):
    Y_plus_X'' = Y_plus_X, Y_minus_X'' = Y_minus_X, Z'' = Z, T2d'' = T2d
  - The operation is constant-time (execution time does not depend on choice value)
-/

/-- **Spec and proof concerning `backend.serial.curve_models.ConditionallySelectableProjectiveNielsPoint.conditional_assign`**:
- No panic (always returns successfully)
- Given inputs:
  • a ProjectiveNielsPoint `self` with coordinates (Y_plus_X, Y_minus_X, Z, T2d),
  • a ProjectiveNielsPoint `other` with coordinates (Y_plus_X', Y_minus_X', Z', T2d'),
  • a Choice `choice`,
the output ProjectiveNielsPoint computed by `conditional_assign self other choice` satisfies:
- Each coordinate is conditionally selected: if choice is 1, output = other; if choice is 0, output = self
- The operation is performed in constant time for all field elements
-/

theorem conditional_assign_spec
    (self other : backend.serial.curve_models.ProjectiveNielsPoint)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ result =>
      (∀ i < 5, result.Y_plus_X[i]!.val =
        if choice.val = 1#u8 then other.Y_plus_X[i]!.val else self.Y_plus_X[i]!.val) ∧
      (∀ i < 5, result.Y_minus_X[i]!.val =
        if choice.val = 1#u8 then other.Y_minus_X[i]!.val else self.Y_minus_X[i]!.val) ∧
      (∀ i < 5, result.Z[i]!.val =
        if choice.val = 1#u8 then other.Z[i]!.val else self.Z[i]!.val) ∧
      (∀ i < 5, result.T2d[i]!.val =
        if choice.val = 1#u8 then other.T2d[i]!.val else self.T2d[i]!.val) ⦄ := by
  sorry

end curve25519_dalek.backend.serial.curve_models.ConditionallySelectableProjectiveNielsPoint
