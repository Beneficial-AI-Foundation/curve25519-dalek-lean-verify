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
open curve25519_dalek.backend.serial.u64.field.FieldElement51

/-! ## Spec for `neg` -/

/-- **Spec for `backend.serial.u64.field.FieldElement51.neg`**:
- No panic (always returns successfully under standard bounds)
- Delegates to `negate`, hence returns the additive inverse modulo p
- Input bound assumption: all limbs of the input are < 2^54 (as in `negate_spec`)
- Output bound matches `negate_spec` -/
@[progress]
theorem neg_spec (r : backend.serial.u64.field.FieldElement51)
    (h : ∀ i < 5, r[i]!.val < 2 ^ 54) :
    neg r ⦃ r_inv =>
    (Field51_as_Nat r + Field51_as_Nat r_inv) % p = 0 ∧
    (∀ i < 5, r_inv[i]!.val ≤ 2^51 + (2^13 - 1) * 19) ⦄ := by
  unfold neg
  -- Use the `negate` specification since `neg` is just a thin wrapper
  progress
  exact ⟨‹_›, ‹_›⟩

end curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
