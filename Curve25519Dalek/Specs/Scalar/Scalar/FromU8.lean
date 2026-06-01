/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::from`

Constructs a `Scalar` from a `u8` value `x` by creating a 32-byte zero-initialized array,
setting byte 0 to `x`, and wrapping the result as a `Scalar`. Because every `u8` value is
less than 2⁸ and 2⁸ < L (the group order, ≈ 2²⁵²), the resulting `Scalar` is automatically
in canonical form.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.CoreConvertFromU8

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::from`**
• The function always succeeds (no panic) for any `u8` input
• The resulting `Scalar`'s byte representation, interpreted as a little-endian natural
  number via `U8x32_as_Nat`, equals `x.val`
• Since `x.val < 2⁸ < L`, the resulting `Scalar` is automatically canonical
-/
@[step]
theorem from_spec (x : U8) :
    «from» x ⦃ (result : Scalar) =>
      U8x32_as_Nat result.bytes = x.val ⦄ := by
  unfold «from»
  simp only [step_simps]
  let* ⟨ s_bytes1, s_bytes1_post ⟩ ← Array.update_spec
  simp_all only
  simp [U8x32_as_Nat, Finset.sum_range_succ]

end curve25519_dalek.scalar.Scalar.Insts.CoreConvertFromU8
