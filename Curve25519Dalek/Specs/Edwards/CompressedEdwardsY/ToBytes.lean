/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-! # Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::to_bytes`

This function copies the internal 32-byte little-endian encoding stored inside a
`CompressedEdwardsY` into a new owned array.

Given a `CompressedEdwardsY` wrapping a `[u8; 32]`, `to_bytes` returns a copy of that
byte array. In Rust this is the owned counterpart of `as_bytes` (which returns a reference).

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.CompressedEdwardsY

/-- **Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::to_bytes`**
• The function succeeds (always returns `ok`)
• The result is exactly the internal byte array representation -/
@[step]
theorem to_bytes_spec (self : CompressedEdwardsY) :
    to_bytes self ⦃ (result : Array U8 32#usize) =>
      result = self ⦄ := by
  unfold to_bytes
  simp

end curve25519_dalek.edwards.CompressedEdwardsY
