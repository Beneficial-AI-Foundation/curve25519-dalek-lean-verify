/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `FieldElement51::ONE`

Specification and proof for `FieldElement51::ONE`.

This constant represents the multiplicative identity element (1) in the field.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
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
theorem ONE_spec : ok ONE ⦃ fe => Field51_as_Nat fe = 1 ⦄ := by
  have h : Field51_as_Nat ONE = 1 := by
    unfold ONE ONE_body eval_global Field51_as_Nat
    decide
  simpa [ONE, ONE_body, eval_global, Field51_as_Nat] using h

end curve25519_dalek.backend.serial.u64.field.FieldElement51
