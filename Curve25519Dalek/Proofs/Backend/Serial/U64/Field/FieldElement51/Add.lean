/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Proofs.Backend.Serial.U64.Field.FieldElement51.AddAssign

/-! # Add

Specification and proof for `FieldElement51::add`.

This function performs element-wise addition of field element limbs. It simply wraps `add_assign`.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-! ## Spec for `add` -/

/-- **Spec for `backend.serial.u64.field.FieldElement51.add`**:
- Does not overflow when limb sums don't exceed U64.max
- Returns a field element where each limb is the sum of corresponding input limbs
- This is element-wise addition, not modular field addition (use reduce for that)
- Simply wraps add_assign -/
@[progress]
theorem add_spec (a b : Array U64 5#usize)
    (hab : ∀ i, i < 5 → (a[i]!).val + (b[i]!).val ≤ U64.max) :
    ∃ result, add a b = ok result ∧
    (∀ i, i < 5 → (result[i]!).val = (a[i]!).val + (b[i]!).val) := by
  unfold add
  exact add_assign_spec a b hab

end curve25519_dalek.backend.serial.u64.field.FieldElement51
