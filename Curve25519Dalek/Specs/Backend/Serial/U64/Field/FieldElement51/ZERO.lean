/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromLimbs

/-! # Spec Theorem for `FieldElement51::ZERO`

Specification and proof for `FieldElement51::ZERO`.

This constant represents the additive identity element (0) in the field.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std.WP Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    • Represents the additive identity element in the field 𝔽_p where p = 2^255 - 19
    • The field element is represented as five u64 limbs: [0, 0, 0, 0, 0]
    • This is the constant field element with value 0

natural language specs:

    • Field51_as_Nat(ZERO) = 0
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.ZERO`**:
- The constant is equal to 0
-/
@[progress]
theorem ZERO_spec : ZERO ⦃ (result : FieldElement51) =>
    Field51_as_Nat result = 0 ⦄ := by
  unfold ZERO
  progress*
  simp only [*]
  decide

end curve25519_dalek.backend.serial.u64.field.FieldElement51
