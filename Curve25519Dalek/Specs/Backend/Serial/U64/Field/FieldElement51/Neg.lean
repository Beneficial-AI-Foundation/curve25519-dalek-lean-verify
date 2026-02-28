/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Negate

/-! # Neg

Specification and proof for `FieldElement51::neg`.

This function performs field element negation by delegating to `negate`.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
open curve25519_dalek.backend.serial.u64.field FieldElement51

/-! ## Spec for `neg` -/

/-- **Spec for `backend.serial.u64.field.FieldElement51.neg`**:
- No panic (always returns successfully under standard bounds)
- Delegates to `negate`, hence returns the additive inverse modulo p
- Input bound assumption: all limbs of the input are < 2^54 (as in `negate_spec`)
- Output bound matches `negate_spec` -/
@[progress]
theorem neg_spec (self : FieldElement51)
    (h : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    neg self ⦃ (neg : FieldElement51) =>
      Field51_as_Nat self + Field51_as_Nat neg ≡ 0 [MOD p] ∧
      ∀ i < 5, neg[i]!.val ≤ 2 ^ 52 ⦄ := by
  unfold neg
  progress*


end curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
