/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.AsBytes

/-!
# Spec theorem for `curve25519_dalek::ristretto::CompressedRistretto::ct_eq`

This function performs constant-time equality comparison of two `CompressedRistretto` values
by converting both to byte arrays via `as_bytes` (identity), converting to slices, and
delegating to the slice-level constant-time comparison.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.CompressedRistretto.Insts.SubtleConstantTimeEq

/-- **Spec theorem for `curve25519_dalek::ristretto::CompressedRistretto::ct_eq`**
• The operation never panics (always returns successfully)
• Returns `Choice.one` iff the two `CompressedRistretto` values are equal
-/
@[step]
theorem ct_eq_spec (self other : CompressedRistretto) :
    ct_eq self other ⦃ (result : subtle.Choice) =>
      result = Choice.one ↔ self = other ⦄ := by
  unfold ct_eq
  step*
  simp_all only [Array.to_slice, Slice.eq_iff]
  exact Subtype.val_injective.eq_iff

end curve25519_dalek.ristretto.CompressedRistretto.Insts.SubtleConstantTimeEq
