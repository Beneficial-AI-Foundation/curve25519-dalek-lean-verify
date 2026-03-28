/-
Copyright 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-! # Spec theorem for `Scalar::from` (From<u8>)

Specification and proof for the `From<u8>` trait implementation for Scalar.

This function constructs a `Scalar` from a `u8` value by writing its 1
little-endian bytes into the first byte of a 32-byte zero array.
Because every `u8` value is less than 2^8, and 2^8 < L (the group order,
≈ 2²⁵²), the resulting `Scalar` is automatically in canonical form.

Source: "curve25519-dalek/src/scalar.rs"
-/
namespace curve25519_dalek.scalar.Scalar.Insts.CoreConvertFromU8

/-
natural language description:

• Takes a u8 value `x`
• Creates a 32-byte array initialized to zero
• Sets byte 0 of the array to `x` (via Array.update at index 0)
• Returns a Scalar wrapping the resulting 32-byte array

natural language specs:

• The function always succeeds (no panic) for any u8 input
• The resulting Scalar's byte representation, interpreted as a little-endian
  natural number via U8x32_as_Nat, equals x.val (the natural number value of x)
• Since x.val < 2^8 < L, the resulting Scalar is automatically canonical
-/

/-- **Spec and proof concerning `scalar.Scalar.Insts.CoreConvertFromU8.from`**:
• The function always succeeds (no panic)
• The resulting Scalar's byte representation equals x.val
  (i.e., U8x32_as_Nat result.bytes = x.val)
• The result is automatically canonical (less than L) since x.val < 2^8 < L
-/
@[progress]
theorem from_spec (x : Std.U8) :
    «from» x ⦃ result =>
    U8x32_as_Nat result.bytes = x.val ⦄ := by
  unfold «from»
  simp only [progress_simps]
  let* ⟨ s_bytes1, s_bytes1_post ⟩ ← Array.update_spec
  simp_all only
  simp [U8x32_as_Nat, Finset.sum_range_succ]

end curve25519_dalek.scalar.Scalar.Insts.CoreConvertFromU8
