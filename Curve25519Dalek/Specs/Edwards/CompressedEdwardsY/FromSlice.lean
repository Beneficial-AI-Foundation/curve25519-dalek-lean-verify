/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.FromSlice

/-!
# Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::from_slice`

Constructs a `CompressedEdwardsY` from a byte slice by attempting to convert
the slice into a 32-byte array via `TryFrom`. If the slice has exactly 32 bytes, it returns
`Ok(CompressedEdwardsY(bytes))`; otherwise it returns `Err(TryFromSliceError)`.

The function never panics — it always succeeds at the Aeneas `Result` level. The inner
`core.result.Result` signals success or failure of the byte-to-array conversion.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.CompressedEdwardsY

/-- **Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::from_slice`**
• The operation never panics (always returns `.ok` at the Aeneas level)
• If `bytes.length = 32`: the `result` is `.Ok cey` where `cey.val = bytes.val`
• If `bytes.length ≠ 32`: the `result` is `.Err ()`
-/
@[step]
theorem from_slice_spec
    (bytes : Slice U8) :
    from_slice bytes ⦃
      (result : core.result.Result CompressedEdwardsY core.array.TryFromSliceError) =>
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
