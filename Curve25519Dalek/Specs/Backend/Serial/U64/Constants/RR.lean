/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

set_option exponentiation.threshold 260

/-! # Spec theorem for `constants::RR`

Specification and proof for the constant `RR`.

This constant represents R² mod L, where R = 2^260 is the Montgomery constant
and L is the group order. It is used in Montgomery form conversions.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::RR`**
Scalar52_as_Nat(constants.RR) ≡ R² (mod L) where R = 2^260. -/
@[simp]
theorem RR_spec : Scalar52_as_Nat RR % _root_.L = _root_.R ^ 2 % _root_.L := by
  unfold RR
  decide

theorem RR_limbs_lt : ∀ j < 5, constants.RR[j]!.val < 2 ^ 52 := by unfold RR; decide

theorem RR_value_lt_L : Scalar52_as_Nat RR < _root_.L := by
  unfold RR Scalar52_as_Nat _root_.L; decide

end curve25519_dalek.backend.serial.u64.constants
