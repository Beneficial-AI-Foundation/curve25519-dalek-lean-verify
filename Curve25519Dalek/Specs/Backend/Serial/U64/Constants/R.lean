/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

set_option exponentiation.threshold 260

/-! # Spec theorem for `constants::R`

Specification and proof for the constant `R`.

This constant represents R mod L, where R = 2^260 is the Montgomery constant
and L is the group order. It is used in Montgomery form conversions.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::R`**
- The value of constants.R when converted to a natural number is congruent to R modulo L -/
@[simp]
theorem R_spec : Scalar52_as_Nat R % _root_.L = _root_.R % _root_.L := by
  unfold R
  decide

theorem R_limbs_lt : ∀ j < 5, constants.R[j]!.val < 2 ^ 52 := by unfold R; decide

theorem R_value_lt_L : Scalar52_as_Nat R < _root_.L := by
  unfold R Scalar52_as_Nat _root_.L; decide

end curve25519_dalek.backend.serial.u64.constants
