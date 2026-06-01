/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
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

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::reduce`

Takes an input scalar `s` and outputs a scalar `s'` representing its canonical reduced form:
`s'` lies in `{0, …, ℓ – 1}` and satisfies `s ≡ s' (mod ℓ)` where `ℓ` is the group order.

Source: "curve25519-dalek/src/scalar.rs"
-/

set_option linter.style.whitespace false -- spaces inside ⟨ ... ⟩ in let* patterns are intentional
set_option exponentiation.threshold 260

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::reduce`**
• No panic (always returns successfully)
• The result scalar `s'` is congruent to the input scalar `s` modulo `L` (the group order)
• The result scalar `s'` is in canonical form (less than `L`)
-/
@[step]
theorem reduce_spec (s : Scalar) :
    reduce s ⦃ (s' : Scalar) =>
      U8x32_as_Nat s'.bytes ≡ U8x32_as_Nat s.bytes [MOD L] ∧
      U8x32_as_Nat s'.bytes < L ⦄ := by
  unfold reduce
  let* ⟨ x, x_post1, x_post2 ⟩ ← unpack_spec
  let* ⟨ xR, xR_post1, xR_post2 ⟩ ← scalar.Scalar52.mul_internal_spec
  · unfold constants.R; decide
  let* ⟨ x_mod_l, x_mod_l_post1, x_mod_l_post2, x_mod_l_post3 ⟩ ←
      scalar.Scalar52.montgomery_reduce_spec
  · -- x < R (from limbs < 2^52), constants.R < L (it's R mod L), so x * R_const < R * L
    rw [xR_post1]
    have h_x_lt : Scalar52_as_Nat x < R := Scalar52_as_Nat_bounded x x_post2
    have h_R_lt : Scalar52_as_Nat constants.R < L := by unfold constants.R Scalar52_as_Nat L; decide
    exact Nat.mul_lt_mul_of_lt_of_lt h_x_lt h_R_lt
  let* ⟨ s', s'_post1, s'_post2 ⟩ ← pack_spec
  simp only [and_true, *]
  rw [← x_post1]
  rw [← Nat.ModEq] at x_mod_l_post1
  rw [xR_post1] at x_mod_l_post1
  have Rs := constants.R_spec
  rw [← Nat.ModEq] at Rs
  have := Nat.ModEq.mul_left (Scalar52_as_Nat x) Rs
  have := Nat.ModEq.trans x_mod_l_post1 this
  apply cancelR
  apply Nat.ModEq.trans (Nat.ModEq.mul_right R s'_post1) this

end curve25519_dalek.scalar.Scalar
