/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `FieldElement51::ONE`

Specification and proof for `FieldElement51::ONE`.

This constant represents the multiplicative identity element (1) in the field.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std.WP Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    • Represents the multiplicative identity element in the field 𝔽_p where p = 2^255 - 19
    • The field element is represented as five u64 limbs: [1, 0, 0, 0, 0]
    • This is the constant field element with value 1

natural language specs:

    • Field51_as_Nat(ONE) = 1
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.ONE`**:
- The constant, when converted to a natural number, equals 1
-/
@[progress]
theorem ONE_spec : ONE ⦃ result => Field51_as_Nat result = 1 ⦄ := by
  unfold ONE from_limbs
  simp only [spec_ok]
  decide

end curve25519_dalek.backend.serial.u64.field.FieldElement51
