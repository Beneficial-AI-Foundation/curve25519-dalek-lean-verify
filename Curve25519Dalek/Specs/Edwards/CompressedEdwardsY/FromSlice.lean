/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.FromSlice
/-! # Spec Theorem for `CompressedEdwardsY::from_slice`

Specification and proof for the `from_slice` method on `CompressedEdwardsY`.

This function constructs a `CompressedEdwardsY` from a byte slice by attempting to convert
the slice into a 32-byte array via `TryFrom`. If the slice has exactly 32 bytes, it returns
`Ok(CompressedEdwardsY(bytes))`; otherwise it returns `Err(TryFromSliceError)`.

The function never panics — it always succeeds at the Aeneas `Result` level. The inner
`core.result.Result` signals success or failure of the byte-to-array conversion.

**Source**: curve25519-dalek/src/edwards.rs

**Dependencies**:
- `core.array.TryFromArrayCopySlice.try_from` (Aeneas library, has definition)
- `core.result.Result.map` (axiom in FunsExternal.lean — needs spec for proof)
- `from_slice.closure.call_once` (identity closure, `ok tupled_args`)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.CompressedEdwardsY

/-
natural language description:

    • Constructs a `CompressedEdwardsY` from a byte slice `bytes`.
    • Internally, tries to convert the slice into a `[u8; 32]` array via `TryFrom`.
    • If the slice has exactly 32 bytes, returns `Ok(CompressedEdwardsY(bytes))`.
    • If the slice does not have exactly 32 bytes, returns `Err(TryFromSliceError)`.
    • The function never panics — it always succeeds at the Aeneas `Result` level.
    • The inner Rust-level `core::result::Result` signals success or failure.

natural language specs:

    • The operation never panics (always returns `ok` at the Aeneas level)
    • If bytes.length = 32: the result is Ok(cey) where cey.val = bytes.val
    • If bytes.length ≠ 32: the result is Err(())
-/

/-- **Spec and proof concerning `edwards.CompressedEdwardsY.from_slice`**:
    • The operation never panics (always returns `ok` at the Aeneas level)
    • If bytes.length = 32: the result is Ok(cey) where cey.val = bytes.val
    • If bytes.length ≠ 32: the result is Err(())
-/
@[step]
theorem from_slice_spec
    (bytes : Slice U8) :
    from_slice bytes ⦃ (result : core.result.Result CompressedEdwardsY
        core.array.TryFromSliceError) =>
      (bytes.length = 32 → ∃ cey : CompressedEdwardsY, result = .Ok cey ∧ cey.val = bytes.val) ∧
      (bytes.length ≠ 32 → result = .Err ()) ⦄ := by
  unfold from_slice
  step
  · exact List.mapM_clone_eq (fun _ _ => by rfl)
  · cases r
    · simp only [core.result.Result.map]
      exact ⟨r_post1, r_post2⟩
    · simp only [core.result.Result.map, spec_ok]
      exact ⟨r_post1, fun _ => trivial⟩

end curve25519_dalek.edwards.CompressedEdwardsY
