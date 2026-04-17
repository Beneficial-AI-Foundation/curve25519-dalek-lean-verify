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
import Curve25519Dalek.Specs.Scalar.Scalar.ConditionalSelect
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

-- Inhabited chain so `step` can apply Aeneas array specs (which require `[Inhabited α]`).
instance : Inhabited (Aeneas.Std.Array U64 5#usize) where
  default := ⟨List.replicate 5 default, by decide⟩

instance : Inhabited curve25519_dalek.backend.serial.u64.field.FieldElement51 where
  default := ⟨List.replicate 5 default, by decide⟩

instance : Inhabited ProjectiveNielsPoint where
  default := ⟨default, default, default, default⟩

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

/-- Two-conjunct wrapper around `Array.update_spec` for `ProjectiveNielsPoint` arrays of length 8.
Provides:
- `arr'[k]! = arr[k]!` for indices `k ≠ j.val`,
- `arr'[j.val]! = v` at the updated index. -/
@[step]
private lemma Array_PNP_8_update_spec (arr : Array ProjectiveNielsPoint 8#usize) (j : Usize)
    (v : ProjectiveNielsPoint) (hj : j.val < 8) :
    Array.update arr j v ⦃ arr' =>
      (∀ (k : ℕ), k ≠ j.val → arr'[k]! = arr[k]!) ∧
      arr'[j.val]! = v ⦄ := by
  have hbound : j.val < arr.length := by scalar_tac
  apply spec_mono (Array.update_spec arr j v hbound)
  intro arr' harr'
  subst harr'
  constructor
  · intro k hk
    simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
    exact List.getElem!_set_ne arr.val j.val k v (Or.inl (Ne.symm hk))
  · simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
    exact List.getElem!_set arr.val j.val v (by scalar_tac)


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
  unfold window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop
  obtain ⟨o, iter1, h_next, h_none_branch, h_some_branch⟩ :=
    curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable.next_spec iter
  rw [h_next, bind_tc_ok]
  match o with
  | none =>
    -- Base case: iter.start.val ≥ iter.end.val = 7, combined with h_start ≤ 7 gives = 7
    have hge : ¬ iter.start.val < iter.end.val := by
      intro hlt
      exact absurd (h_some_branch hlt).1 (by simp)
    have hstart7 : iter.start.val = 7 := by omega
    simp only [spec_ok]
    refine ⟨?_, ?_⟩
    · intro k
      apply h_prefix_valid k
      have := k.isLt; omega
    · intro k
      apply h_prefix_point k
      have := k.isLt; omega
  | some j =>
    have hlt : iter.start.val < iter.end.val := by
      by_contra hge
      exact absurd (h_none_branch hge).1 (by simp)
    obtain ⟨hj_eq_some, hiter1_start, hiter1_end⟩ := h_some_branch hlt
    have hj_val : j.val = iter.start.val := by
      have h : some j = some iter.start := hj_eq_some
      exact congrArg UScalar.val (Option.some.inj h)
    have hj_lt7 : j.val < 7 := by omega
    have hj_lt8 : j.val < 8 := by omega
    -- Step 1: Array.index_usize — retrieve pnp = points[j]
    step as ⟨pnp, hpnp_eq⟩
    -- Bridge: Aeneas' `Array.index_usize_spec` exposes `[k]!` (List.getElem!), but our
    -- invariant uses `Fin`-based `[⟨k, hk⟩]`. Bridge once and reuse for IsValid + toPoint.
    have hlen : j.val < (↑points : List ProjectiveNielsPoint).length := by
      have := points.2; simp_all
    have hpnp_bridge : (↑points : List ProjectiveNielsPoint)[j.val]! =
        (↑points : List ProjectiveNielsPoint)[(⟨j.val, hj_lt8⟩ : Fin 8)] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
      agrind only [= Fin.getElem_fin]
    have hjFin : (⟨j.val, hj_lt8⟩ : Fin 8).val < iter.start.val + 1 := by
      change j.val < _; omega
    -- pnp.IsValid from the prefix invariant
    have hpnp_valid : pnp.IsValid := by
      rw [hpnp_eq, hpnp_bridge]
      exact h_prefix_valid ⟨j.val, hj_lt8⟩ hjFin
    -- pnp.toPoint equals (j.val + 1) • P.toPoint
    have hpnp_point : pnp.toPoint = (j.val + 1) • P.toPoint := by
      rw [hpnp_eq, hpnp_bridge]
      exact h_prefix_point ⟨j.val, hj_lt8⟩ hjFin
    -- Step 2: CompletedPoint.add — cp = P + pnp
    step as ⟨cp, hcp_valid, hcp_eq⟩
    -- Step 3: CompletedPoint.as_extended — ep (extended form of cp)
    step as ⟨ep, hep1, hep2, hep3, hep4, hep5, hep6, hep7, hep_valid, hep_eq, hep_cp⟩
    -- Step 4: EdwardsPoint.as_projective_niels — pnp1 (niels form of ep)
    step as ⟨pnp, hpnp1, hpnp2, hpnp3, hpnp4, hpnp1_valid, hpnp1_eq⟩
    -- rename_i pnp1
    -- Step 5: i_next = j + 1
    step as ⟨i_next, hi_next_val⟩
    -- Step 6: Array.update — a = points.set i_next pnp1
    have hi_next_lt8 : i_next.val < 8 := by
      have : i_next.val = j.val + 1 := by scalar_tac
      omega
    let* ⟨ a, a_post1, a_post2 ⟩ ← Array_PNP_8_update_spec
    let* ⟨ result, result_post1, result_post2 ⟩ ← from_loop_spec
    · sorry
    · sorry
    agrind

    -- step with Array_PNP_8_update_spec points i_next hpnp1 hi_next_lt8
    --   as ⟨a, ha_other, ha_curr⟩
    -- Establish new invariants for iter1
    -- have hiter1_start_val : iter1.start.val = j.val + 1 := by
    --   rw [hiter1_start, hj_val]
    -- have hi_next_val_eq : i_next.val = j.val + 1 := by scalar_tac
    -- -- Prefix IsValid for iter1
    -- have h_prefix_valid' : ∀ (k : Fin 8), k.val < iter1.start.val + 1 →
    --     a.val[k].IsValid := by
    --   intro k hk
    --   rw [hiter1_start_val] at hk
    --   by_cases hkeq : k.val = i_next.val
    --   · -- k = i_next = j + 1: a[k] = pnp1
    --     have h1 : a.val[k] = pnp1 := by
    --       have := ha_curr
    --       simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, getElem?_pos,
    --         Option.getD_some] at this
    --       rw [hkeq] at *
    --       have hkFin : k.val = i_next.val := hkeq
    --       -- a.val[k] = a.val[i_next.val] = pnp1
    --       rw [show k.val = i_next.val from hkeq] at *
    --       exact this
    --     rw [h1]; exact hpnp1_valid
    --   · -- k ≠ i_next: a[k] = points[k], use h_prefix_valid
    --     have h1 : a.val[k] = points.val[k] := by
    --       have := ha_other k.val hkeq
    --       simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, getElem?_pos,
    --         Option.getD_some] at this
    --       exact this
    --     rw [h1]
    --     apply h_prefix_valid k
    --     omega
    -- -- Prefix toPoint for iter1
    -- have h_prefix_point' : ∀ (k : Fin 8), k.val < iter1.start.val + 1 →
    --     a.val[k].toPoint = (k.val + 1) • P.toPoint := by
    --   intro k hk
    --   rw [hiter1_start_val] at hk
    --   by_cases hkeq : k.val = i_next.val
    --   · -- k = j + 1: a[k] = pnp1, derive pnp1.toPoint = (j+2) • P
    --     have h1 : a.val[k] = pnp1 := by
    --       have := ha_curr
    --       simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, getElem?_pos,
    --         Option.getD_some] at this
    --       rw [show k.val = i_next.val from hkeq] at *
    --       exact this
    --     rw [h1]
    --  -- Build the chain: pnp1.toPoint = ep.toPoint = cp.toPoint = P + pnp = P + (j+1)•P = (j+2)•P
    --     rw [← hpnp1_eq, hep_eq, hcp_eq, hpnp_point]
    --     -- (j.val + 1) • P.toPoint + P.toPoint = (j.val + 2) • P.toPoint
    --     have hkval : k.val = j.val + 1 := by rw [hkeq]; exact hi_next_val_eq
    --     rw [hkval]
    --     rw [show j.val + 1 + 1 = j.val + 2 from rfl]
    --     rw [add_comm P.toPoint]
    --     rw [show (j.val + 2 : ℕ) • P.toPoint = (j.val + 1) • P.toPoint + P.toPoint by
    --       rw [show j.val + 2 = (j.val + 1) + 1 from rfl, succ_nsmul]]
    --   · -- k ≠ j + 1: a[k] = points[k], use h_prefix_point
    --     have h1 : a.val[k] = points.val[k] := by
    --       have := ha_other k.val hkeq
    --       simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, getElem?_pos,
    --         Option.getD_some] at this
    --       exact this
    --     rw [h1]
    --     apply h_prefix_point k
    --     omega
    -- -- Preconditions for the IH
    -- have h_start' : iter1.start.val ≤ 7 := by
    --   rw [hiter1_start_val]; omega
    -- have h_end' : iter1.«end».val = 7 := by
    --   rw [hiter1_end]; exact h_end
    -- -- Apply the IH
    -- apply spec_mono
    --   (from_loop_spec P hP iter1 a h_start' h_end' h_prefix_valid' h_prefix_point')
    -- intro result hresult
    -- exact hresult
    -- simp_wf
    -- rw [hiter1_start, hiter1_end]
    -- omega

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
