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

open Aeneas Aeneas.Std Aeneas.Std.WP Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Takes an input Scalar s and returns another Scalar s' that
      represents the multiplicative inverse of s within the underlying
      field \mathbb{Z} / \ell \mathbb{Z}.

natural language specs:

    • \forall Scalars s with scalar_to_nat(s) ≢ 0 (mod \ell):
      scalar_to_nat(s) * scalar_to_nat(s') is congruent to 1 (mod \ell) -/

/-- **Spec and proof concerning `scalar.Scalar.invert`**:
- Precondition: The input scalar s must be non-zero modulo L (inverting zero has undefined behavior)
- No panic (returns successfully for non-zero input)
- The result s' satisfies the multiplicative inverse property:
  U8x32_as_Nat(s.bytes) * U8x32_as_Nat(s'.bytes) ≡ 1 (mod L) -/
@[step]
theorem invert_spec (self : Scalar) (h : U8x32_as_Nat self.bytes % L ≠ 0) :
    invert self ⦃ (result : Scalar) =>
      U8x32_as_Nat self.bytes * U8x32_as_Nat result.bytes ≡ 1 [MOD L] ⦄ := by
  unfold invert
  let* ⟨ s, s_post1, s_post2 ⟩ ← unpack_spec
  let* ⟨ s1, s1_post1, s1_post2, s1_post3 ⟩ ← Scalar52.invert_spec
  let* ⟨ result, result_post1, result_post2 ⟩ ← Scalar52.pack_spec
  calc U8x32_as_Nat self.bytes * U8x32_as_Nat result.bytes
      ≡ Scalar52_as_Nat s * U8x32_as_Nat result.bytes [MOD L] := by
        exact Nat.ModEq.mul_right _ (by rw [s_post1])
    _ ≡ Scalar52_as_Nat s * Scalar52_as_Nat s1 [MOD L] := by
        exact Nat.ModEq.mul_left _ result_post1
    _ ≡ 1 [MOD L] := s1_post1


end curve25519_dalek.scalar.Scalar
