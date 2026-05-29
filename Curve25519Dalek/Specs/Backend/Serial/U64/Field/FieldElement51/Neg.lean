/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Negate

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::neg`

This function performs field element negation by delegating to `negate`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field FieldElement51
namespace curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::neg`**
• The function always succeeds (no panic) provided every input limb is `< 2 ^ 54`
• `Field51_as_Nat self + Field51_as_Nat neg ≡ 0 (mod p)`, i.e. `neg` is the additive inverse
• Every output limb is `< 2 ^ 52`
-/
@[step]
theorem neg_spec (self : FieldElement51)
    (h : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    neg self ⦃ (neg : FieldElement51) =>
      Field51_as_Nat self + Field51_as_Nat neg ≡ 0 [MOD p] ∧
      ∀ i < 5, neg[i]!.val < 2 ^ 52 ⦄ := by
  unfold neg
  step*

end curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
