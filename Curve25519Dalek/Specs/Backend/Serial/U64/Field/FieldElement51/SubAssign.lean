/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub

/-! # Spec Theorem for `FieldElement51::sub_assign`

Specification and proof for `FieldElement51::sub_assign`.

This function performs field element subtraction assignment. In the Rust implementation,
this would modify the first operand in-place. In Lean, since values are immutable,
this simply calls `sub` and returns the result.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    • Takes two input FieldElement51s a and b and returns another FieldElement51
      that is a representant of the difference a - b in the field (modulo p = 2^255 - 19).

    • The implementation directly delegates to `sub`.

natural language specs:

    • For all FieldElement51s a and b:
      Field51_as_Nat(sub_assign(a, b)) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p)
      where p = 2^255 - 19
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.sub_assign`**:
- No panic (always succeeds since it delegates to `sub`)
- The result c satisfies the field subtraction property:
  Field51_as_Nat(c) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p)
  where p = 2^255 - 19
-/
@[progress]
theorem sub_assign_spec (a b : Array U64 5#usize) :
    ∃ c, sub_assign a b = ok c ∧
    Field51_as_Nat c % p = (Field51_as_Nat a - Field51_as_Nat b) % p := by
  unfold sub_assign
  progress*

end curve25519_dalek.backend.serial.u64.field.FieldElement51
