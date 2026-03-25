/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub

/-! # Spec Theorem for `FieldElement51::sub_assign`

Specification and proof for `FieldElement51::sub_assign`.

This function performs field element subtraction assignment. In the Rust implementation,
this would modify the first operand in-place. In Lean, since values are immutable,
this simply calls `sub` and returns the result.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithSubAssignSharedAFieldElement51

/-
natural language description:

    • Takes two input FieldElement51s a and b and returns another FieldElement51
      that is a representant of the difference a - b in the field (modulo p = 2^255 - 19).

    • The implementation directly delegates to `sub`.

natural language specs:

    • For appropriately bounded FieldElement51s a and b:
      Field51_as_Nat(sub_assign(a, b)) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p), or equivalently
      Field51_as_Nat(sub_assign(a, b)) + Field51_as_Nat(b) ≡ Field51_as_Nat(a) (mod p)
-/

@[progress]
theorem sub_assign_spec (self _rhs : backend.serial.u64.field.FieldElement51)
    (ha : ∀ i < 5, self[i]!.val < 2 ^ 63)
    (hb : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    sub_assign self _rhs ⦃ (result : backend.serial.u64.field.FieldElement51) =>
      (∀ i < 5, result[i]!.val < 2 ^ 52) ∧
      (Field51_as_Nat result + Field51_as_Nat _rhs) % p = Field51_as_Nat self % p ⦄ := by
  unfold sub_assign
  progress*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithSubAssignSharedAFieldElement51
