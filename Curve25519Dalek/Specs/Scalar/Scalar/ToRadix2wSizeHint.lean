/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::to_radix_2w_size_hint`

This function returns a **size hint** — an upper bound on the number of
nonzero digits produced by `to_radix_2w(w)` — for a radix-`2^w`
representation of a scalar, with `w ∈ {4, 5, 6, 7, 8}`.

The formula is:
  - For `4 ≤ w ≤ 7`:  `digits_count = ⌈256 / w⌉ = (256 + w − 1) / w`
  - For `w = 8`:      `digits_count = ⌈256 / 8⌉ + 1 = 33`
    (the extra `+1` accounts for a possible terminal carry digit that can
    arise when the scalar satisfies invariant #1 but not #2, i.e.,
    `2^252 ≤ scalar < 2^255`)

In all valid cases, the result is at most 64.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::to_radix_2w_size_hint`**
• The function always succeeds (no panic) for any `w` with `4 ≤ w ≤ 8`.
• For `4 ≤ w ≤ 7`: the result equals `(256 + w - 1) / w`.
• For `w = 8`: the result equals `(256 + 8 - 1) / 8 + 1 = 33`.
• In all cases, the result is at most 64.
-/
@[step]
theorem to_radix_2w_size_hint_spec (w : Usize)
    (h_lo : 4 ≤ w.val) (h_hi : w.val ≤ 8) :
    to_radix_2w_size_hint w ⦃ (result : Usize) =>
      (w.val ≤ 7 → result.val = (256 + w.val - 1) / w.val) ∧
      (w.val = 8 → result.val = (256 + 8 - 1) / 8 + 1) ∧
      result.val ≤ 64 ⦄ := by
  unfold to_radix_2w_size_hint
  step (config := { maxSteps := 1 })
  step (config := { maxSteps := 1 })
  split_ifs with hw
  · step*
    simp_all
    have hw_pos : 0 < w.val := by omega
    have h65 : (255 + w.val) / ↑w < 65 := by
      rw [Nat.div_lt_iff_lt_mul hw_pos]
      linarith
    linarith
  · step (config := { maxSteps := 1 })
    step*

end curve25519_dalek.scalar.Scalar
