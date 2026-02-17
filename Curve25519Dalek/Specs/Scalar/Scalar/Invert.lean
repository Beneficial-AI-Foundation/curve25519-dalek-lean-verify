/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.TypesAux
import Curve25519Dalek.Specs.Scalar.Scalar.Unpack
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack

/-! # Spec Theorem for `Scalar::invert`

Specification and proof for `Scalar::invert`.

This function computes the multiplicative inverse.

Source: curve25519-dalek/src/scalar.rs
-/

open Aeneas.Std Aeneas.Std.WP Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Takes an input Scalar s and returns another Scalar s' that
      represents the multiplicative inverse of s within the underlying
      field \mathbb{Z} / \ell \mathbb{Z}.

natural language specs:

    • \forall Scalars s with scalar_to_nat(s) ≢ 0 (mod \ell):
      scalar_to_nat(s) * scalar_to_nat(s') is congruent to 1 (mod \ell)
-/

lemma ZERO_eq : Scalar52_as_Nat backend.serial.u64.scalar.Scalar52.ZERO = 0 := by
  unfold backend.serial.u64.scalar.Scalar52.ZERO backend.serial.u64.scalar.Scalar52.ZERO_body
  decide

/-- **Spec and proof concerning `scalar.Scalar.invert`**:
- Precondition: The input scalar s must be non-zero modulo L (inverting zero has undefined behavior)
- No panic (returns successfully for non-zero input)
- The result s' satisfies the multiplicative inverse property:
  U8x32_as_Nat(s.bytes) * U8x32_as_Nat(s'.bytes) ≡ 1 (mod L)
-/
@[progress]
theorem invert_spec (s : Scalar) (h : U8x32_as_Nat s.bytes % L ≠ 0) :
    spec (invert s) (fun s' =>
    U8x32_as_Nat s.bytes * U8x32_as_Nat s'.bytes ≡ 1 [MOD L]) := by
  sorry
/- OLD PROOF (before Aeneas WP migration):
  unfold invert
  progress*
  -- BEGIN TASK
  rw [← s_post_1]
  have := Nat.ModEq.mul_left (Scalar52_as_Nat s) res_post_1
  exact Nat.ModEq.trans this s1_post
  -- END TASK
-/


end curve25519_dalek.scalar.Scalar
