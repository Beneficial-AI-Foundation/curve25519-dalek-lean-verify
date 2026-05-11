/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::ristretto::CompressedRistretto::as_bytes`

Extracts the 32-byte array representation `[u8; 32]` from a `CompressedRistretto`. Since
`CompressedRistretto` is a type alias for `Array U8 32#usize` in Lean, this is essentially an
identity operation that returns the underlying byte array unchanged.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.CompressedRistretto

/-- **Spec theorem for `curve25519_dalek::ristretto::CompressedRistretto::as_bytes`**
• The operation never panics (always returns successfully)
• as_bytes self = self, i.e., the function is the identity on `CompressedRistretto`
-/
@[step]
theorem as_bytes_spec (self : CompressedRistretto) :
    as_bytes self ⦃ (result : Array U8 32#usize) =>
      result = self ⦄ := by
  unfold as_bytes
  simp

end curve25519_dalek.ristretto.CompressedRistretto
