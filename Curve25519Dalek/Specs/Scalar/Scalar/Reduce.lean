/-
Copyright (c) 2025 Beneficial AI Foundation.
All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Scalar.Scalar.Unpack
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.R
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Invert

/-!
# Specification and Theorem for `Scalar::reduce`

This file provides a formal specification and proof for the `Scalar::reduce` function
in the Curve25519-dalek library.

`Scalar::reduce` performs modular reduction of a `Scalar`.

**Source**: `curve25519-dalek/src/scalar.rs`
-/

set_option linter.style.commandStart false
set_option exponentiation.threshold 260

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.scalar.Scalar52

namespace curve25519_dalek.scalar.Scalar

/-!
## Natural Language Description

- Input: a `Scalar` `s`
- Output: a `Scalar` `s'` in canonical form such that:
  - `s'` is congruent to `s` modulo the group order `ℓ`
  - `s' ∈ {0, …, ℓ − 1}`
-/

--! ## Natural language specification
--! * scalar_to_nat(s) ≡ scalar_to_nat(s') mod ℓ
--! * scalar_to_nat(s') ∈ {0, …, ℓ − 1}

/--
Spec and proof concerning `Scalar.reduce`:

- Always succeeds (no panic)
- Result scalar `s'` is congruent to input `s` modulo `L` (group order)
- Result scalar `s'` is canonical (less than `L`)
-/
theorem cancelR {a b : ℕ} (h : a * R ≡ b * R [MOD L]) : a ≡ b [MOD L] := by
  have hcoprime : Nat.Coprime R L := by
    unfold R L Nat.Coprime
    simp
  have h1 := Nat.Coprime.symm hcoprime
  exact Nat.ModEq.cancel_right_of_coprime h1 h

@[progress]
theorem reduce_spec (s : Scalar) :
    ∃ s',
      reduce s = ok s' ∧
      U8x32_as_Nat s'.bytes ≡ U8x32_as_Nat s.bytes [MOD L] ∧
      U8x32_as_Nat s'.bytes < L
    := by
  unfold reduce
  progress*
  · unfold constants.R; decide
  simp[res_post_2]
  rw[← x_post_2]
  rw[← Nat.ModEq] at x_mod_l_post
  rw[xR_post] at x_mod_l_post
  have Rs := R_spec
  rw[← Nat.ModEq] at Rs
  have := Nat.ModEq.mul_left (Scalar52_as_Nat x) Rs
  have := Nat.ModEq.trans x_mod_l_post this
  apply cancelR
  apply Nat.ModEq.trans (Nat.ModEq.mul_right R res_post_1) this

end curve25519_dalek.scalar.Scalar
