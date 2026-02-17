/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect

/-! # ConditionalSelect

Specification for `ProjectivePoint::conditional_select`.

This function returns either `a` or `b` depending on the constant-time `Choice` flag.
It applies conditional selection to both the U and W coordinates independently using
`FieldElement51::conditional_select`, which returns the first operand when `choice = 0`
and the second operand when `choice = 1`.

**Source**: curve25519-dalek/src/montgomery.rs:L311-L320
-/

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable

/--
**Spec for `montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select`**:
- No panic (always returns successfully)
- For both U and W coordinates:
  - Each limb of the result equals the corresponding limb from `b` when `choice = 1`
  - Each limb of the result equals the corresponding limb from `a` when `choice = 0`
- Consequently, when `choice = Choice.one` (value 1), the whole result equals `b`;
  when `choice = Choice.zero` (value 0), the result equals `a`.

This implements constant-time conditional selection for Montgomery curve points
in projective coordinates (U:W).
-/
@[progress]
theorem conditional_select_spec
    (a b : montgomery.ProjectivePoint)
    (choice : subtle.Choice) :
    spec (conditional_select a b choice) (fun res =>
      (∀ i < 5, res.U[i]! = (if choice.val = 1#u8 then b.U[i]! else a.U[i]!)) ∧
      (∀ i < 5, res.W[i]! = (if choice.val = 1#u8 then b.W[i]! else a.W[i]!))) := by
  unfold conditional_select
  progress*

end curve25519_dalek.montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable
