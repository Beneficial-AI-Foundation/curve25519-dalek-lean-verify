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

/-- Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::sub_assign`
• The function always succeeds (no panic) provided `self[i].val < 2^63` and `_rhs[i].val < 2^54`
• Every output limb is `< 2 ^ 52`
• `Field51_as_Nat result + Field51_as_Nat _rhs ≡ Field51_as_Nat self (mod p)`,
  i.e. the result represents `self - _rhs` modulo `p` -/
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
