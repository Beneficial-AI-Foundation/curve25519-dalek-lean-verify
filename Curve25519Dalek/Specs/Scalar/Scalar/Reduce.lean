/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Scalar.Scalar.Unpack
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.R
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Invert
/-! # Spec Theorem for `Scalar::reduce`

Specification and proof for `Scalar::reduce`.

This function performs modular reduction.

**Source**: curve25519-dalek/src/scalar.rs
-/

set_option linter.style.commandStart false
set_option exponentiation.threshold 260

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Takes an input Scalar s and outputs a Scalar s’ that represents
      the canonical reduced version, i.e.,  s’ \in \{0, …, \ell – 1}
      and s is congruent to s’ modulo \ell.

natural language specs:

    • scalar_to_nat(s) is congruent to scalar_to_nat(s') modulo \ell
    • scalar_to_nat(s') \in \{0,…, \ell - 1}
-/

/-- **Spec and proof concerning `scalar.Scalar.reduce`**:
- No panic (always returns successfully)
- The result scalar s' is congruent to the input scalar s modulo L (the group order)
- The result scalar s' is in canonical form (less than L)
-/
theorem cancelR {a b : ℕ} (h : a * R ≡ b * R [MOD L]) : a ≡ b [MOD L] := by
  have hcoprime : Nat.Coprime R L := by
    unfold R L Nat.Coprime
    simp
  have h1 := Nat.Coprime.symm hcoprime
  exact Nat.ModEq.cancel_right_of_coprime h1 h

@[progress]
theorem reduce_spec (s : Scalar) :
    reduce s ⦃ s' =>
      U8x32_as_Nat s'.bytes ≡ U8x32_as_Nat s.bytes [MOD L] ∧
      U8x32_as_Nat s'.bytes < L ⦄ := by
  unfold reduce
  progress*
  · unfold constants.R; decide
  simp [*]
  rw [← x_post_1]
  rw [← Nat.ModEq] at x_mod_l_post_1
  rw [xR_post_1] at x_mod_l_post_1
  have Rs := constants.R_spec
  rw [← Nat.ModEq] at Rs
  have := Nat.ModEq.mul_left (Scalar52_as_Nat x) Rs
  have := Nat.ModEq.trans x_mod_l_post_1 this
  apply cancelR
  apply Nat.ModEq.trans (Nat.ModEq.mul_right R res_post_1) this

end curve25519_dalek.scalar.Scalar
