/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjectiveNiels
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
import Curve25519Dalek.ExternallyVerified
import Mathlib

/-! # Spec Theorem for `LookupTable::from`

Specification for the `From<&EdwardsPoint>` implementation for
`LookupTable<ProjectiveNielsPoint>`.

Given an Edwards point `P`, this constructs a lookup table of 8 entries
`[P, 2P, 3P, ..., 8P]` represented as `ProjectiveNielsPoint`s. The table is
built iteratively: starting from `points[0] = P`, each subsequent entry is
computed as `points[j+1] = (P + points[j]).as_extended().as_projective_niels()`,
which yields `(j+2)·P` in `ProjectiveNielsPoint` form.

**Source**: curve25519-dalek/src/window.rs (inside `impl_lookup_table!` macro, ~lines 99-107)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.edwards

namespace curve25519_dalek
namespace window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint

/-
natural language description:

• Takes an EdwardsPoint P and produces a `LookupTable<ProjectiveNielsPoint>` of length 8
whose k-th entry (for k ∈ {0, 1, ..., 7}) equals (k+1)·P in ProjectiveNielsPoint form.

• The construction iterates j = 0, 1, ..., 6 and writes
  points[j+1] = (P + points[j]).as_extended().as_projective_niels()
  starting from points[0] = P.as_projective_niels(), which represents 1·P = P.

natural language specs:

• The function always succeeds (no panic).
• Every entry of the resulting lookup table is a valid ProjectiveNielsPoint.
• For each k ∈ {0, 1, ..., 7}, result[k].toPoint = (k+1) • P.toPoint as points on Ed25519.
-/

/-- Loop spec for `from_loop`: given a `points` array whose prefix `[0, iter.start.val]`
(i.e. `iter.start.val + 1` entries) already holds `[P, 2P, ..., (iter.start.val + 1)P]` as
valid `ProjectiveNielsPoint`s, the loop extends the prefix to cover all 8 indices.

Loop invariant at entry: for every `k ≤ iter.start.val`, `points[k].IsValid` and
`points[k].toPoint = (k + 1) • P.toPoint`. At exit, the invariant holds up to index 7.

The loop body computes
`points[j+1] = (P + points[j]).as_extended().as_projective_niels()`
which turns `(j+1)·P` at index `j` into `(j+2)·P` at index `j+1`. -/
@[step]
theorem from_loop_spec
    (P : EdwardsPoint) (hP : P.IsValid)
    (iter : core.ops.range.Range Std.Usize)
    (points : Array ProjectiveNielsPoint 8#usize)
    (h_start : iter.start.val ≤ 7) (h_end : iter.«end».val = 7)
    (h_prefix_valid : ∀ (k : Fin 8), k.val < iter.start.val + 1 → points.val[k].IsValid)
    (h_prefix_point : ∀ (k : Fin 8), k.val < iter.start.val + 1 →
        points.val[k].toPoint = (k.val + 1) • P.toPoint) :
    window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop
        iter P points ⦃ (result : Array ProjectiveNielsPoint 8#usize) =>
      (∀ (k : Fin 8), result.val[k].IsValid) ∧
      (∀ (k : Fin 8), result.val[k].toPoint = (k.val + 1) • P.toPoint) ⦄ := by
  sorry

/-- **Spec and proof concerning `window.LookupTable<ProjectiveNielsPoint>::from`**:
- No panic (always returns successfully).
- Every entry of the resulting 8-element lookup table is a valid `ProjectiveNielsPoint`.
- For each k ∈ {0, 1, ..., 7}, the k-th entry represents `(k+1) • P` on the Ed25519 curve. -/
@[step]
theorem from_spec (P : EdwardsPoint) (hP : P.IsValid) :
    window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from
        P ⦃ (result : window.LookupTable ProjectiveNielsPoint) =>
      (∀ (k : Fin 8), result.val[k].IsValid) ∧
      (∀ (k : Fin 8), result.val[k].toPoint = (k.val + 1) • P.toPoint) ⦄ := by
  sorry

end window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint
end curve25519_dalek
