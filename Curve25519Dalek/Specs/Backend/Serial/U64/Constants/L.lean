/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `constants::L`

Specification and proof for the constant `L`.

This constant represents the group order L of Curve25519.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::constants::L`**

Scalar52_as_Nat(constants.L) = L where L is the group order. -/
@[simp]
theorem L_spec : Scalar52_as_Nat L = _root_.L := by
  unfold L
  decide

-- Helper lemma to bound the limbs of L without unfolding it everywhere
lemma L_limbs_spec (i : Usize) (h : i.val < 5) :
    (constants.L[i.val]!).val < 2 ^ 52 := by
  unfold constants.L
  rcases h_idx : i.val with _ | _ | _ | _ | _ | n <;> try decide
  rw [h_idx] at h
  contradiction

end curve25519_dalek.backend.serial.u64.constants
