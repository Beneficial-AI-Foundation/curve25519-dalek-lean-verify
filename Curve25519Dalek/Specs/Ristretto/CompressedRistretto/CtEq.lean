/-
Copyright 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.AsBytes

/-!
# Spec theorem for `CompressedRistretto::ct_eq`

Specification and proof for the `ConstantTimeEq` trait implementation for `CompressedRistretto`.

This function performs constant-time equality comparison of two `CompressedRistretto` values
by converting both to byte arrays via `as_bytes` (identity), converting to slices, and
delegating to the slice-level constant-time comparison.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.CompressedRistretto.Insts.SubtleConstantTimeEq

/-
natural language description:

    • Compares two CompressedRistretto values for equality in constant time.

    • Extracts the underlying 32-byte arrays via `as_bytes` (identity operation),
      converts them to slices, and delegates to slice-level constant-time equality.

natural language specs:

    • The operation never panics (always returns successfully)
    • Returns Choice.one iff the two CompressedRistretto values are equal
-/

/-- **Spec and proof concerning `ristretto.CompressedRistretto.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully)
- The result is Choice.one iff the two CompressedRistretto values are equal
-/
@[progress]
theorem ct_eq_spec
    (self other : CompressedRistretto) :
    ct_eq self other ⦃ (result : subtle.Choice) =>
      result = Choice.one ↔ self = other ⦄ := by
  unfold ct_eq
  progress*
  simp_all only [Array.to_slice, Slice.eq_iff]
  exact Subtype.val_injective.eq_iff

end curve25519_dalek.ristretto.CompressedRistretto.Insts.SubtleConstantTimeEq
