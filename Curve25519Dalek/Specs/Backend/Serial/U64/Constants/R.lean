/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::R`

This constant represents R mod L, where R = 2^260 is the Montgomery constant
and L is the group order. It is used in Montgomery form conversions.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

set_option exponentiation.threshold 260

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::R`**
• `Scalar52_as_Nat R ≡ R (mod L)`, i.e. the 5-limb encoding represents the Montgomery
  constant `R = 2^260` modulo the group order `L` -/
@[simp]
theorem R_spec : Scalar52_as_Nat R % _root_.L = _root_.R % _root_.L := by
  unfold R
  decide

theorem R_limbs_lt : ∀ j < 5, R[j]!.val < 2 ^ 52 := by unfold R; decide

theorem R_value_lt_L : Scalar52_as_Nat R < _root_.L := by
  unfold R Scalar52_as_Nat _root_.L; decide

end curve25519_dalek.backend.serial.u64.constants
