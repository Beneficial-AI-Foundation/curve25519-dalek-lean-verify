/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
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

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::invert`

Takes an input Scalar `s` and returns a Scalar `s'` representing the multiplicative inverse
of `s` in the field ℤ/ℓℤ.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::invert`**
• No panic (succeeds for any non-zero scalar; inverting zero is undefined)
• The result satisfies `U8x32_as_Nat self.bytes * U8x32_as_Nat result.bytes ≡ 1 [MOD L]`
-/
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
