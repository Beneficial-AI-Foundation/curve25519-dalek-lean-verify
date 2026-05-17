/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::sub_assign`

This function performs field-element subtraction-assignment on `FieldElement51`. In Rust it
modifies the first operand in place; in this Lean extraction values are immutable, so it
simply delegates to `sub` and returns the result.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreOpsArithSubAssignSharedAFieldElement51

/-- Spec theorem for
`curve25519_dalek::backend::serial::u64::field::FieldElement51::sub_assign`
• For appropriately bounded FieldElement51s a and b:
  Field51_as_Nat(sub_assign(a, b)) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p), or equivalently
  Field51_as_Nat(sub_assign(a, b)) + Field51_as_Nat(b) ≡ Field51_as_Nat(a) (mod p)
-/
@[step]
theorem sub_assign_spec (self _rhs : backend.serial.u64.field.FieldElement51)
    (ha : ∀ i < 5, self[i]!.val < 2 ^ 63)
    (hb : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    sub_assign self _rhs ⦃ (result : backend.serial.u64.field.FieldElement51) =>
      (∀ i < 5, result[i]!.val < 2 ^ 52) ∧
      (Field51_as_Nat result + Field51_as_Nat _rhs) % p = Field51_as_Nat self % p ⦄ := by
  unfold sub_assign
  step*

end CoreOpsArithSubAssignSharedAFieldElement51
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
