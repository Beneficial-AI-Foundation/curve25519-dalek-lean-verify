/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `constants::LFACTOR`

Specification and proof for the constant `LFACTOR`.

This constant satisfies the key property that L * LFACTOR ≡ -1 (mod 2^52), where L is the
group order.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.LFACTOR is a single u64 value (not a multi-limb scalar) such that
      L*constants.LFACTOR + 1 is divisible by 2^52.
    • Used in the montgomery_reduce function

natural language specs:

    • (L * LFACTOR.val) ≡ -1 (mod 2^52)
    • Equivalently: (L * LFACTOR.val + 1) is divisible by 2^52
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.LFACTOR`**:
- The value of LFACTOR satisfies: L * LFACTOR ≡ -1 (mod 2^52)
- LFACTOR is in the range [0, 2^52 - 1]
-/
@[progress]
theorem LFACTOR_spec :
    ok LFACTOR ⦃ _ =>
      (_root_.L * LFACTOR + 1) % (2^52) = 0 ∧
      0 ≤ LFACTOR.val ∧
      LFACTOR.val < 2^52 ⦄ := by
  have h :
      (_root_.L * LFACTOR + 1) % (2^52) = 0 ∧
      0 ≤ LFACTOR.val ∧
      LFACTOR.val < 2^52 := by
    unfold LFACTOR
    decide
  simpa using h

end curve25519_dalek.backend.serial.u64.constants
