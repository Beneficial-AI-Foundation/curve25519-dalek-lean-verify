/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::LFACTOR`

This constant satisfies the key property that L * LFACTOR ≡ -1 (mod 2^52), where L
is the group order.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::LFACTOR`**
• (L * LFACTOR + 1) % 2^52 = 0
• LFACTOR.val lies in the range [0, 2^52) -/
theorem LFACTOR_spec :
      (_root_.L * LFACTOR + 1) % (2^52) = 0 ∧
      0 ≤ LFACTOR.val ∧
      LFACTOR.val < 2^52 := by
  unfold LFACTOR
  decide

end curve25519_dalek.backend.serial.u64.constants
