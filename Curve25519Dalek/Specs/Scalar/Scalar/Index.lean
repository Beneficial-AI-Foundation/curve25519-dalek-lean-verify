/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::index`

Indexes the little-endian byte representation of a `Scalar`, returning the byte at position
`_index`. The `Scalar` is stored as a 32-byte array (`[u8; 32]`), so the index must satisfy
`_index < 32`. Mutation is not permitted (read-only access).

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::index`**
• The function succeeds (no panic) when `_index < 32`
• The result equals `self.bytes[_index]`, the byte at the given position
-/
@[step]
theorem index_spec (self : scalar.Scalar) (_index : Std.Usize)
    (h_bound : _index.val < 32) :
    index self _index ⦃ (result : Std.U8) =>
      result = self.bytes.val[_index.val]! ⦄ := by
  unfold index
  step*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8
