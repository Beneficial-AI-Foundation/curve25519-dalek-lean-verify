/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect




/-! # Spec Theorem for `ProjectiveNielsPoint::conditional_select`

Specification and proof for `ProjectiveNielsPoint::conditional_select`.

This function conditionally selects between two ProjectiveNielsPoint values
based on a Choice flag. It is implemented by applying
`FieldElement51::conditional_select` component-wise to the coordinates
(Y_plus_X, Y_minus_X, Z, T2d), returning `b` when choice = 1 and `a` when
choice = 0, in constant time.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 297:4-304:5
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.curve_models.ConditionallySelectableProjectiveNielsPoint

/--
**Spec and proof concerning `backend.serial.curve_models.ProjectiveNielsPoint.conditional_select`**:
- No panic (always returns successfully)
- Given inputs:
  • ProjectiveNielsPoint `a` with coordinates (Y_plus_X, Y_minus_X, Z, T2d),
  • ProjectiveNielsPoint `b` with coordinates (Y_plus_X', Y_minus_X', Z', T2d'),
  • a Choice `choice`,
  the output ProjectiveNielsPoint has coordinates selected component-wise:
  - If choice = 1, each coordinate equals the corresponding one of `b`
  - If choice = 0, each coordinate equals the corresponding one of `a`
  - The operation is constant-time (does not branch on choice)
-/
theorem conditional_select_spec
    (a b : backend.serial.curve_models.ProjectiveNielsPoint)
    (choice : subtle.Choice) :
    ∃ result, conditional_select a b choice = ok result ∧
    (∀ i < 5, result.Y_plus_X[i]!.val =
      if choice.val = 1#u8 then b.Y_plus_X[i]!.val else a.Y_plus_X[i]!.val) ∧
    (∀ i < 5, result.Y_minus_X[i]!.val =
      if choice.val = 1#u8 then b.Y_minus_X[i]!.val else a.Y_minus_X[i]!.val) ∧
    (∀ i < 5, result.Z[i]!.val =
      if choice.val = 1#u8 then b.Z[i]!.val else a.Z[i]!.val) ∧
    (∀ i < 5, result.T2d[i]!.val =
      if choice.val = 1#u8 then b.T2d[i]!.val else a.T2d[i]!.val) := by
  unfold conditional_select
  progress*
  grind

end curve25519_dalek.backend.serial.curve_models.ConditionallySelectableProjectiveNielsPoint
