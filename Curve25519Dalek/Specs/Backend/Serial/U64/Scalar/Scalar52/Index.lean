/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::index`

Indexes a `Scalar52` by `usize`, returning the `u64` limb at position `_index`. A `Scalar52`
is stored as a 5-element array (`[u64; 5]`), representing a scalar in radix-2⁵² form, so the
index must satisfy `_index < 5`. Mutation is not permitted (read-only access).

Source: "curve25519-dalek/src/backend/serial/u64/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::index`**
• The function succeeds (no panic) when `_index < 5`
• The result equals `self.val[_index]`, the limb at the given position
-/
@[step]
theorem index_spec (self : backend.serial.u64.scalar.Scalar52) (_index : Std.Usize)
    (h_bound : _index.val < 5) :
    index self _index ⦃ (result : Std.U64) =>
      result = self.val[_index.val]! ⦄ := by
  unfold index
  step*

end curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64
