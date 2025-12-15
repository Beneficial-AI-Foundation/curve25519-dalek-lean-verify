/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.AddAssign

/-! # Add

Specification and proof for `FieldElement51::add`.

This function performs element-wise addition of field element limbs. It simply wraps `add_assign`.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field.FieldElement51.AddAssign

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Add

/-! ## Spec for `add` -/

/-- **Spec for `backend.serial.u64.field.FieldElement51.add`**:
- Does not overflow when limb sums don't exceed U64.max
- Returns a field element where each limb is the sum of corresponding input limbs
- This is element-wise addition, not modular field addition (use reduce for that)
- Input bounds: both inputs have limbs < 2^53
- Output bounds: output has limbs < 2^54
- Simply wraps add_assign -/
@[progress]
theorem add_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 53) (hb : ∀ i < 5, b[i]!.val < 2 ^ 53) :
    ∃ result, add a b = ok result ∧
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^54) := by
  unfold add;
  progress*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Add
