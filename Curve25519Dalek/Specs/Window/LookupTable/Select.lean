/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Specs.Window.LookupTable.From
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.Identity
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.Neg
import Curve25519Dalek.ExternallyVerified
import Mathlib

/-! # Spec Theorem for `LookupTable<ProjectiveNielsPoint>::select`

Specification for `LookupTable::select`, specialised to `ProjectiveNielsPoint`.

Given a valid precomputed table `[P, 2P, ..., 8P]` (in `ProjectiveNielsPoint` form)
and a signed nibble `x ∈ [-8, 8]`, `select` returns (a representation of) `x • P`
in constant time. The body computes `|x|` via a sign-mask trick and then:

1. `t = identity` (= `0·P`);
2. for `j ∈ {1,...,8}`, conditionally copies `table[j-1]` onto `t` when `|x| = j`;
3. conditionally negates `t` when `x < 0`.

**Source**: curve25519-dalek/src/window.rs, lines 55-78 (inside `impl_lookup_table!` macro).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.edwards

namespace curve25519_dalek
namespace window.LookupTable

/-
natural language description:

• Input: a `LookupTable<ProjectiveNielsPoint>` that encodes `[1•P, 2•P, ..., 8•P]`
  for some base EdwardsPoint `P`, and a signed 8-bit integer `x` with `-8 ≤ x ≤ 8`.

• Computes the projective-Niels representation of `x • P` in constant time:
  1. Let `xmask = x >> 7` (0 if `x ≥ 0`, −1 if `x < 0`; arithmetic shift).
  2. Let `xabs = (x + xmask) XOR xmask = |x|`.
  3. Initialise `t = identity` (0•P).
  4. For `j ∈ {1, ..., 8}`, conditionally copy `table[j-1]` onto `t` when `|x| = j`.
     After the loop, `t = |x| • P` (or identity if `|x| = 0`).
  5. Let `neg_mask = xmask & 1` (= 1 iff `x < 0`).
  6. Conditionally replace `t` with `-t` if `neg_mask = 1`, producing `x • P`.

natural language specs:

• The function always succeeds (no panic) given `-8 ≤ x ≤ 8`.
• The result is a valid `ProjectiveNielsPoint`.
• The result represents `(x.val : ℤ) • P.toPoint` on Ed25519.
-/

/-! ## Helper: Inhabited instance (reuse) -/

-- `Inhabited ProjectiveNielsPoint` is already provided in `Window/LookupTable/From.lean`.

/-! ## Spec for `LookupTable<ProjectiveNielsPoint>::select` -/

/-- **Spec and proof concerning `window.LookupTable<ProjectiveNielsPoint>::select`**:
- No panic (always returns successfully) on inputs with `-8 ≤ x ≤ 8`.
- The returned `ProjectiveNielsPoint` is valid.
- It represents `(x.val : ℤ) • P.toPoint`, where `P` is the EdwardsPoint used to
  construct the table (so `table[k].toPoint = (k+1) • P.toPoint` for `k ∈ Fin 8`).

This follows the Rust semantics literally:
`selected.toPoint = (sign of x) • (|x| • P) = x • P`. -/
@[step]
theorem select_spec {P : EdwardsPoint}
    (table : window.LookupTable ProjectiveNielsPoint)
    (h_table_valid : ∀ (k : Fin 8), table.val[k].IsValid)
    (h_table_point : ∀ (k : Fin 8),
        table.val[k].toPoint = ((k.val + 1 : ℕ) : ℤ) • P.toPoint)
    (x : Std.I8)
    (h_bounds_lo : -8 ≤ x.val) (h_bounds_hi : x.val ≤ 8) :
    window.LookupTable.select
        ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity
        ProjectiveNielsPoint.Insts.SubtleConditionallySelectable
        ProjectiveNielsPoint.Insts.CoreMarkerCopy
        ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint
        table x ⦃ (selected : ProjectiveNielsPoint) =>
      selected.IsValid ∧
      selected.toPoint = (x.val : ℤ) • P.toPoint ⦄ := by
  unfold select
  simp only [step_simps]
  let* ⟨ hx ⟩ ← massert_spec
  let* ⟨ i, i_post ⟩ ← IScalar.cast.step_spec
  let* ⟨ _ ⟩ ← massert_spec
  · simp only [i_post, IScalar.le_equiv, IScalarTy.I8_numBits_eq, IScalarTy.I16_numBits_eq,
    Nat.reduceLeDiff, IScalar.val_mod_pow_greater_numBits]; agrind
  let* ⟨ i1, i1_post ⟩ ← IScalar.cast.step_spec
  sorry
  -- Proof strategy (to be completed; see `.formalising/fv-plans/.continue-here.md`):
  --
  --  1. Unfold `select`. Show the two `massert`s succeed (bounds on x).
  --  2. Identify `xmask.val = if x.val < 0 then -1 else 0` and `xabs.val = |x.val|`
  --     via arithmetic on I16. (`>>> 7` on I16 is arithmetic shift.)
  --  3. Step through `identity`; obtain initial `t` with `t.IsValid ∧ t.toPoint = 0`.
  --  4. Dispatch a `select_loop_spec` with loop invariant
  --       `t.IsValid ∧ t.toPoint = if |x|.val ∈ [1..iter.start.val) then
  --                                  ((|x|.val - 1 : ℕ) + 1 : ℤ) • P.toPoint
  --                                else 0`
  --     which, since the iterator runs `start = 1`, `end = 9`, yields after exit
  --       `t.toPoint = if |x|.val ∈ [1..8] then (|x|.val : ℤ) • P.toPoint else 0`
  --     i.e. `t.toPoint = (|x.val| : ℤ) • P.toPoint` for all `|x.val| ∈ [0..8]`.
  --  5. Compute `neg_mask`: it is `Choice.one` iff `x.val < 0`, else `Choice.zero`.
  --  6. Apply `neg_spec` to get `t_neg.IsValid ∧ t_neg.toPoint = -t.toPoint`.
  --  7. Apply a point-level `conditional_assign_spec` to combine: result matches
  --     `t` or `t_neg` depending on `neg_mask`, then push `toPoint` through.
  --  8. Conclude `selected.toPoint = sign(x) · |x| · P.toPoint = x.val • P.toPoint`
  --     via `Int.sign_mul_natAbs` / `zsmul` identities.


end window.LookupTable
end curve25519_dalek
