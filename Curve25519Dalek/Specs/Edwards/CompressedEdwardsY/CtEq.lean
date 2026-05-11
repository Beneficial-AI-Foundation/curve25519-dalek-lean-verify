/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.AsBytes

/-!
# Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::ct_eq`

Compares two `CompressedEdwardsY` values for equality in constant time by extracting
the underlying 32-byte arrays via `as_bytes` (an identity operation), converting them
to slices, and delegating to the slice-level constant-time equality comparison.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq

/-- **Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::ct_eq`**
• The operation never panics (always returns successfully)
• Returns `Choice.one` iff the two `CompressedEdwardsY` values are equal
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
