/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::index_mut`

Mutably indexes a `Scalar52` by `usize`, returning the `u64` limb at position `_index` together
with a write-back function that produces an updated `Scalar52` with the limb at `_index` replaced
by a new value. A `Scalar52` is stored as a 5-element array (`[u64; 5]`), representing a scalar
in radix-2⁵² form, so the index must satisfy `_index < 5`.

Source: "curve25519-dalek/src/backend/serial/u64/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::index_mut`**
• The function succeeds (no panic) when `_index < 5`
• The first component of the result equals `self.val[_index]`, the limb at the given position
• The second component is `Array.set self _index`, which replaces the limb at position `_index`
-/
@[step]
theorem index_mut_spec (self : backend.serial.u64.scalar.Scalar52) (_index : Std.Usize)
    (h_bound : _index.val < 5) :
    index_mut self _index ⦃ (result : Std.U64 × (Std.U64 → backend.serial.u64.scalar.Scalar52)) =>
      result.1 = self.val[_index.val]! ∧
      result.2 = Aeneas.Std.Array.set self _index ⦄ := by
  unfold index_mut
  step*

end curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64
