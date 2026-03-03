/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `CompressedRistretto::from_slice`

Specification and proof for the `from_slice` method on `CompressedRistretto`.

This function constructs a `CompressedRistretto` from a byte slice by attempting to convert
the slice into a 32-byte array via `TryFrom`. If the slice has exactly 32 bytes, it returns
`Ok(CompressedRistretto(bytes))`; otherwise it returns `Err(TryFromSliceError)`.

The function never panics — it always succeeds at the Aeneas `Result` level. The inner
`core.result.Result` signals success or failure of the byte-to-array conversion.

**Source**: curve25519-dalek/src/ristretto.rs, lines 245:4-248:5

**Dependencies**:
- `core.array.TryFromArrayCopySlice.try_from` (Aeneas library, has definition)
- `core.result.Result.map` (axiom in FunsExternal.lean — needs spec for proof)
- `from_slice.closure.call_once` (identity closure, `ok tupled_args`)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.CompressedRistretto

/-
natural language description:

    • Constructs a `CompressedRistretto` from a byte slice `bytes`.
    • Internally, tries to convert the slice into a `[u8; 32]` array via `TryFrom`.
    • If the slice has exactly 32 bytes, returns `Ok(CompressedRistretto(bytes))`.
    • If the slice does not have exactly 32 bytes, returns `Err(TryFromSliceError)`.
    • The function never panics — it always succeeds at the Aeneas `Result` level.
    • The inner Rust-level `core::result::Result` signals success or failure.

natural language specs:

    • The operation never panics (always returns `ok` at the Aeneas level)
    • If bytes.length = 32: the result is Ok(cr) where cr.val = bytes.val
    • If bytes.length ≠ 32: the result is Err(())
-/

/-- **Spec and proof concerning `ristretto.CompressedRistretto.from_slice`**:
    • The operation never panics (always returns `ok` at the Aeneas level)
    • If bytes.length = 32: the result is Ok(cr) where cr.val = bytes.val
    • If bytes.length ≠ 32: the result is Err(())
-/
@[progress]
theorem from_slice_spec (bytes : Slice Std.U8) :
    from_slice bytes ⦃ r =>
    (bytes.length = 32 →
      ∃ cr : CompressedRistretto, r = .Ok cr ∧ cr.val = bytes.val) ∧
    (bytes.length ≠ 32 →
      r = .Err ()) ⦄ := by
  sorry

end curve25519_dalek.ristretto.CompressedRistretto
