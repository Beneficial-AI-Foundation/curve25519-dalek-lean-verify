/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::ristretto::CompressedRistretto::from_slice`

This function constructs a `CompressedRistretto` from a byte slice by attempting to convert
the slice into a 32-byte array via `TryFrom`. If the slice has exactly 32 bytes, it returns
`Ok(CompressedRistretto(bytes))`; otherwise it returns `Err(TryFromSliceError)`.

The function never panics; it always succeeds at the Aeneas `Result` level. The inner
`core.result.Result` signals success or failure of the byte-to-array conversion.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-- **Spec theorem for `core::array::TryFromArrayCopySlice::try_from`**
• The operation never panics (always returns `ok` at the Aeneas level)
• If slice length matches N: returns `Ok` with the same values
• If slice length ≠ N: returns `Err`
-/
@[step]
theorem core.array.TryFromArrayCopySlice.try_from_spec
    {T : Type} (N : Usize) (copyInst : core.marker.Copy T) (s : Slice T)
    (hClone : List.mapM copyInst.cloneInst.clone s.val = ok s.val) :
    core.array.TryFromArrayCopySlice.try_from N copyInst s
    ⦃ (result : core.result.Result (Array T N) core.array.TryFromSliceError) =>
      (s.length = N → ∃ a : Array T N, result = .Ok a ∧ a.val = s.val) ∧
      (s.length ≠ N → result = .Err ()) ⦄ := by
  unfold core.array.TryFromArrayCopySlice.try_from
  split
  · split
    · simp_all only [ok.injEq, forall_const, ne_eq, not_true_eq_false,
                     IsEmpty.forall_iff, and_true, spec_ok,
                     core.result.Result.Ok.injEq, exists_eq_left']
    · simp_all only [reduceCtorEq]
    · simp_all only [reduceCtorEq]
  · simp only [spec_ok, reduceCtorEq, false_and, exists_false, implies_true, and_true]
    assumption

namespace curve25519_dalek.ristretto.CompressedRistretto

/-- **Spec theorem for `curve25519_dalek::ristretto::CompressedRistretto::from_slice`**
• The operation never panics (always returns `ok` at the Aeneas level)
• If bytes.length = 32: the result is Ok(cr) where cr.val = bytes.val
• If bytes.length ≠ 32: the result is Err(())
-/
@[step]
theorem from_slice_spec (bytes : Slice U8) :
    from_slice bytes ⦃
      (result : core.result.Result CompressedRistretto core.array.TryFromSliceError) =>
      (bytes.length = 32 → ∃ cr : CompressedRistretto, result = .Ok cr ∧ cr.val = bytes.val) ∧
      (bytes.length ≠ 32 → result = .Err ()) ⦄ := by
  unfold from_slice
  step
  · exact List.mapM_clone_eq (fun _ _ => by rfl)
  · cases r
    · simp only [core.result.Result.map]
      exact ⟨r_post1, r_post2⟩
    · simp only [core.result.Result.map, spec_ok]
      exact ⟨r_post1, fun _ => trivial⟩

end curve25519_dalek.ristretto.CompressedRistretto
