/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
/-! # Spec Theorem for `Scalar::to_radix_2w_size_hint`

Specification and proof for `Scalar::to_radix_2w_size_hint`.

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

**Source**: curve25519-dalek/src/scalar.rs (lines 1036:4-1056:5)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

• Takes a window size `w : Usize` with `4 ≤ w ≤ 8`.
• Checks the two preconditions via `massert`; panics if violated.
• Computes the digit count:
    - If `w ≤ 7`: `digits_count = (256 + w − 1) / w`
    - If `w = 8`: `digits_count = (256 + w − 1) / w + 1`
  (The `if w ≤ 7 … else massert (w = 8) …` branching is how the Aeneas
   extraction renders the original Rust `if w <= 7 { … } else { … }` because
   Aeneas cannot lower `usize` match arms via dependent elimination.)
• Checks `digits_count ≤ 64` via `massert`.
• Returns `digits_count`.

natural language specs:

• The function always succeeds (no panic) for any `w` with `4 ≤ w ≤ 8`.
• For `4 ≤ w ≤ 7`: the result equals `(256 + w - 1) / w`.
• For `w = 8`:       the result equals `(256 + 8 - 1) / 8 + 1 = 33`.
• In all cases, the result is at most 64.
-/

/-- **Spec and proof concerning `scalar.Scalar.to_radix_2w_size_hint`**:

**Proof sketch**:
  After discharging the two bound `massert`s with `h_lo` and `h_hi`, we split
  on the `if w ≤ 7` branch.
  - **Branch `w ≤ 7`**: arithmetic on machine `Usize` is non-overflowing for
    all `w ∈ {4,…,7}` (since `256 + 7 = 263 ≪ 2^64`), so `step*` reduces
    each let-binding and the final `massert` follows by `omega`.
  - **Branch `w = 8`**: the nested `massert (w = 8)` is satisfied, then the
    same arithmetic argument gives `digits_count = 33 ≤ 64`.
  In both cases `ok digits_count` is returned and the postcondition is
  witnessed by the computed value.
-/
@[step]
theorem to_radix_2w_size_hint_spec (w : Std.Usize)
    (h_lo : 4 ≤ w.val) (h_hi : w.val ≤ 8) :
    to_radix_2w_size_hint w ⦃ result =>
      (w.val ≤ 7 → result.val = (256 + w.val - 1) / w.val) ∧
      (w.val = 8 → result.val = (256 + 8 - 1) / 8 + 1) ∧
      result.val ≤ 64 ⦄ := by
  unfold to_radix_2w_size_hint
  step (config := { maxSteps := 1 })
  step (config := { maxSteps := 1 })
  split_ifs with hw
  · step*
    · simp_all
      have hw_pos : 0 < w.val := by omega
      have h65 : (255 + w.val) / ↑w < 65 := by
        rw [Nat.div_lt_iff_lt_mul hw_pos]
        linarith
      linarith
    · constructor
      · simp_all
      · constructor
        · simp_all
          grind
        · simp_all
          have hw_pos : 0 < w.val := by omega
          have h65 : (255 + w.val) / ↑w < 65 := by
            rw [Nat.div_lt_iff_lt_mul hw_pos]
            linarith
          linarith
  · step (config := { maxSteps := 1 })
    step*
    have : w.val = 8:= by scalar_tac
    simp_all

end curve25519_dalek.scalar.Scalar
