/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.AsBytes

/-! # Spec Theorem for `CompressedEdwardsY::ct_eq`

Specification and proof for the `ConstantTimeEq` trait implementation for `CompressedEdwardsY`.

This function performs constant-time equality comparison of two `CompressedEdwardsY` values
by converting both to byte arrays via `as_bytes` (identity), converting to slices, and
delegating to the slice-level constant-time comparison.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq

/-
natural language description:

    • Compares two CompressedEdwardsY values for equality in constant time.

    • Extracts the underlying 32-byte arrays via `as_bytes` (identity operation),
      converts them to slices, and delegates to slice-level constant-time equality.

natural language specs:

    • The operation never panics (always returns successfully)
    • Returns Choice.one iff the two CompressedEdwardsY values are equal
-/

/-- **Spec and proof concerning `edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully)
- The result is Choice.one iff the two CompressedEdwardsY values are equal
-/
@[step]
theorem ct_eq_spec
    (self other : CompressedEdwardsY) :
    ct_eq self other ⦃ (result : subtle.Choice) =>
      result = Choice.one ↔ self = other ⦄ := by
  unfold ct_eq
  step*
  simp_all only [Array.to_slice, Slice.eq_iff]
  exact Subtype.val_injective.eq_iff

end curve25519_dalek.edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq
