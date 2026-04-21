/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Aux
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

/-! ## Helpers: I16 arithmetic operations for the sign-mask trick -/

/-- Arithmetic shift right of an I16 by 7 bits.
For `i ∈ [-8, 8]`, the result is `-1` if `i < 0` and `0` otherwise.
This is the `xmask = x >> 7` step in `select`. Modelled on
`isize_shiftRight_4_spec` in `Specs/Scalar/Scalar/AsRadix16.lean`. -/
@[step]
private theorem i16_shiftRight_7 (i : Std.I16)
    (h_lo : -8 ≤ i.val) (h_hi : i.val ≤ 8) :
    i >>> 7#i32 ⦃ r =>
      r.val = i.val / 128 ∧
      (r.val = -1 ∨ r.val = 0) ∧
      (r.val = -1 ↔ i.val < 0) ⦄ := by
  simp only [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar,
             IScalar.shiftRight, IScalar.toNat, IScalar.val]
  norm_num
  have h7_eq : (7#IScalarTy.I32.numBits).toInt.toNat = 7 := by decide
  simp only [h7_eq]
  have hmatch : i.val >>> (7 : Nat) = i.val / 128 := by
    rw [Int.shiftRight_eq_div_pow]; norm_num
  have h_val_eq : (i.bv.sshiftRight 7).toInt = i.val / 128 := by
    rw [BitVec.sshiftRight_eq]
    rw [BitVec.toInt_ofInt]
    rw [I16.bv_toInt_eq]
    rw [hmatch]
    exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 15 (i.val / 128)
      (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · change (i.bv.sshiftRight 7).toInt = i.val / 128
    exact h_val_eq
  · change (i.bv.sshiftRight 7).toInt = -1 ∨ (i.bv.sshiftRight 7).toInt = 0
    rw [h_val_eq]
    rcases lt_or_ge i.val 0 with hneg | hnn
    · left; omega
    · right; omega
  · change (i.bv.sshiftRight 7).toInt = -1 ↔ i.val < 0
    rw [h_val_eq]
    omega

/-! ## Loop spec for `LookupTable<ProjectiveNielsPoint>::select_loop` -/

/-- **Spec for `window.LookupTable<ProjectiveNielsPoint>::select_loop`**:

Given a valid table `[P, 2P, ..., 8P]` (in `ProjectiveNielsPoint` form) and an
iterator `iter` with `iter.start.val = s ∈ [1, 9]`, `iter.«end».val = 9`:

- At entry, if the loop has already examined `j ∈ [1, s)` and found a match
  (i.e., `xabs.val ∈ [1, s)`), then `t.toPoint = xabs.val • P.toPoint`; otherwise
  `t.toPoint = 0`. (At `s = 1` this is just `t.toPoint = 0`.)

- At exit (`s = 9`), since `xabs.val ∈ [0, 8]`:
  - if `xabs.val ∈ [1, 8]`: the loop matched, `t.toPoint = xabs.val • P.toPoint`;
  - if `xabs.val = 0`: no match, `t.toPoint = 0 = 0 • P.toPoint`.
  Both cases collapse to `result.toPoint = xabs.val • P.toPoint`.

Body of one iteration with `j = iter.start.val`:
1. `ct_eq xabs j` returns `Choice.one` iff `xabs.val = j.val`;
2. `table[j - 1]` gives `j • P` (valid);
3. `conditional_assign t table[j-1] c`: picks `table[j-1]` iff match, else keeps `t`;
4. recurse with iterator advanced (`iter1.start = s + 1`). -/
@[step]
theorem select_loop_spec {P : EdwardsPoint}
    (table : window.LookupTable ProjectiveNielsPoint)
    (h_table_valid : ∀ (k : Fin 8), table.val[k].IsValid)
    (h_table_point : ∀ (k : Fin 8),
        table.val[k].toPoint = ((k.val + 1 : ℕ) : ℤ) • P.toPoint)
    (iter : core.ops.range.Range Std.Usize)
    (h_start_lo : 1 ≤ iter.start.val) (h_start_hi : iter.start.val ≤ 9)
    (h_end : iter.«end».val = 9)
    (xabs : Std.I16) (h_xabs_lo : 0 ≤ xabs.val) (h_xabs_hi : xabs.val ≤ 8)
    (t : ProjectiveNielsPoint) (h_t_valid : t.IsValid)
    (h_t_point : t.toPoint =
        (if 1 ≤ xabs.val ∧ xabs.val < (iter.start.val : ℤ)
          then (xabs.val : ℤ) • P.toPoint else 0)) :
    window.LookupTable.select_loop
        ProjectiveNielsPoint.Insts.SubtleConditionallySelectable
        iter table xabs t ⦃ (result : ProjectiveNielsPoint) =>
      result.IsValid ∧ result.toPoint = (xabs.val : ℤ) • P.toPoint ⦄ := by
  unfold window.LookupTable.select_loop
  obtain ⟨o, iter1, h_next, h_none_branch, h_some_branch⟩ :=
    curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable.next_spec iter
  rw [h_next, bind_tc_ok]
  match o with
  | none =>
    -- Base case: iter.start.val ≥ iter.end.val = 9, with h_start_hi ≤ 9 forces = 9.
    have hge : ¬ iter.start.val < iter.«end».val := by
      intro hlt
      exact absurd (h_some_branch hlt).1 (by simp)
    have hstart9 : iter.start.val = 9 := by omega
    simp only [spec_ok]
    refine ⟨h_t_valid, ?_⟩
    rw [h_t_point, hstart9]
    push_cast
    -- Collapse invariant: xabs.val ∈ [0, 8], so either xabs.val = 0 (0•P = 0) or xabs.val ∈ [1, 8].
    by_cases hx : xabs.val = 0
    · simp [hx]
    · have hxge1 : (1 : ℤ) ≤ xabs.val := by omega
      have hxlt9 : xabs.val < (9 : ℤ) := by omega
      simp [hxge1, hxlt9]
  | some j =>
    have hlt : iter.start.val < iter.«end».val := by
      by_contra hge
      exact absurd (h_none_branch hge).1 (by simp)
    obtain ⟨hj_eq_some, hiter1_start, hiter1_end⟩ := h_some_branch hlt
    have hj_val : j.val = iter.start.val := by
      have h : some j = some iter.start := hj_eq_some
      exact congrArg UScalar.val (Option.some.inj h)
    have hj_lo : 1 ≤ j.val := by omega
    have hj_hi : j.val ≤ 8 := by omega
    have hj_lt9 : j.val < 9 := by omega
    simp only [step_simps]
    -- Step 1: i ← hcast .U16 xabs
    have hxabs_U16 : (0 : ℤ) ≤ xabs.val ∧ xabs.val ≤ UScalar.max .U16 := by
      refine ⟨h_xabs_lo, ?_⟩
      simp only [UScalar.max]; agrind
    let* ⟨ i, i_post ⟩ ← IScalar.hcast_inBounds_spec
    -- Step 2: i1 ← cast .U16 j
    have hj_U16 : j.val ≤ UScalar.max .U16 := by
      simp only [UScalar.max]; agrind
    let* ⟨ i1, i1_post ⟩ ← UScalar.cast_inBounds_spec
    -- Step 3: c ← ct_eq i i1
    let* ⟨ c, c_post ⟩ ← U16.Insts.SubtleConstantTimeEq.ct_eq_spec
    -- Step 4: i2 ← j - 1
    let* ⟨ i2, i2_post ⟩ ← Usize.sub_spec
    -- Bridge: i2.val = j.val - 1 ∈ [0, 7].
    have hi2_val : i2.val = j.val - 1 := by omega
    have hi2_lt8 : i2.val < 8 := by omega
    -- Step 5: t1 ← Array.index_usize table i2
    let* ⟨ t1, t1_post ⟩ ← Array.index_usize_spec
    -- Bridge: t1 = table[i2.val]! = table.val[⟨i2.val, _⟩].
    have hlen : i2.val < (↑table : List ProjectiveNielsPoint).length := by
      have := table.2; simp_all
    have ht1_bridge : (↑table : List ProjectiveNielsPoint)[i2.val]! =
        (↑table : List ProjectiveNielsPoint)[(⟨i2.val, hi2_lt8⟩ : Fin 8)] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
      agrind only [= Fin.getElem_fin]
    have ht1_valid : t1.IsValid := by
      rw [t1_post, ht1_bridge]; exact h_table_valid ⟨i2.val, hi2_lt8⟩
    have ht1_point : t1.toPoint = ((i2.val + 1 : ℕ) : ℤ) • P.toPoint := by
      rw [t1_post, ht1_bridge]; exact h_table_point ⟨i2.val, hi2_lt8⟩
    -- Step 6: t2 ← conditional_assign t t1 c (our point-level wrapper)
    let* ⟨ t2, t2_valid, t2_point ⟩ ←
      ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_assign_point
    -- Setup iter1 preconditions for recursive call.
    have hiter1_start_val : iter1.start.val = j.val + 1 := by rw [hiter1_start, hj_val]
    have h_start_lo' : 1 ≤ iter1.start.val := by rw [hiter1_start_val]; omega
    have h_start_hi' : iter1.start.val ≤ 9 := by rw [hiter1_start_val]; omega
    have h_end' : iter1.«end».val = 9 := by rw [hiter1_end]; exact h_end
    -- Bridge: c.val = 1#u8 ↔ xabs.val = j.val (as ℤ).
    have hi1_int : (i1.val : ℤ) = (j.val : ℤ) := by exact_mod_cast i1_post
    have hi_eq_i1_iff : i = i1 ↔ xabs.val = (j.val : ℤ) := by
      constructor
      · intro heq
        have : (i.val : ℤ) = (i1.val : ℤ) := by rw [heq]
        rw [i_post, hi1_int] at this; exact this
      · intro heq
        apply UScalar.eq_of_val_eq
        have : (i.val : ℤ) = (i1.val : ℤ) := by rw [i_post, hi1_int, heq]
        exact_mod_cast this
    have hc_val_xabs_iff : c.val = 1#u8 ↔ xabs.val = (j.val : ℤ) := by
      rw [Choice.val_eq_one_iff, c_post, hi_eq_i1_iff]
    -- Establish t2's toPoint invariant for the recursive call.
    have h_t2_point_inv : t2.toPoint =
        (if 1 ≤ xabs.val ∧ xabs.val < (iter1.start.val : ℤ)
          then (xabs.val : ℤ) • P.toPoint else 0) := by
      rw [t2_point, hiter1_start_val]
      push_cast
      by_cases hmatch : xabs.val = (j.val : ℤ)
      · -- Match: c.val = 1, t2 = t1, condition holds.
        have hcv : c.val = 1#u8 := hc_val_xabs_iff.mpr hmatch
        have hxge1 : (1 : ℤ) ≤ xabs.val := by rw [hmatch]; exact_mod_cast hj_lo
        have hxlt_jp1 : xabs.val < ((j.val : ℤ) + 1) := by rw [hmatch]; omega
        simp only [hcv, if_true, hxge1, hxlt_jp1, and_self]
        rw [ht1_point, hi2_val]
        have : ((j.val - 1 + 1 : ℕ) : ℤ) = xabs.val := by
          rw [Nat.sub_add_cancel hj_lo]; exact hmatch.symm
        rw [this]
      · -- No match: c.val = 0, t2 = t, new invariant from old.
        have hcv : c.val ≠ 1#u8 := fun h => hmatch (hc_val_xabs_iff.mp h)
        simp only [hcv, if_false]
        rw [h_t_point, hj_val]
        have hxabs_ne : xabs.val ≠ (iter.start.val : ℤ) := by rw [← hj_val]; exact hmatch
        by_cases hxge : 1 ≤ xabs.val
        · by_cases hxlt : xabs.val < ((iter.start.val : ℤ))
          · have hxlt' : xabs.val < ((iter.start.val : ℤ) + 1) := by omega
            simp only [hxge, hxlt, hxlt', and_self, if_true]
          · push_neg at hxlt
            have hxnlt' : ¬ (xabs.val < ((iter.start.val : ℤ) + 1)) := by omega
            have hxnlt : ¬ (xabs.val < (iter.start.val : ℤ)) := not_lt.mpr hxlt
            simp only [hxge, hxnlt, hxnlt', and_false, if_false]
        · simp only [hxge, false_and, if_false]
    apply spec_mono (select_loop_spec table h_table_valid h_table_point iter1
      h_start_lo' h_start_hi' h_end' xabs h_xabs_lo h_xabs_hi t2 t2_valid h_t2_point_inv)
    intro result hresult
    exact hresult
  termination_by iter.«end».val - iter.start.val
  decreasing_by
    rw [hiter1_start, hiter1_end]
    grind

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
  -- Bridge: casting I8 → I16 preserves val.
  have hi1_val : i1.val = x.val := by
    simp only [i1_post, IScalarTy.I8_numBits_eq, IScalarTy.I16_numBits_eq,
      Nat.reduceLeDiff, IScalar.val_mod_pow_greater_numBits]
  let* ⟨ xmask, xmask_post1, xmask_post2, xmask_post3 ⟩ ← i16_shiftRight_7
  let* ⟨ i2, i2_post ⟩ ← IScalar.cast.step_spec
  let* ⟨ i3, i3_post ⟩ ← I16.add_spec
  let* ⟨ xabs, xabs_post1, xabs_post2 ⟩ ← IScalar.xor_spec
  let* ⟨ t, t_post1, t_post2, t_post3, t_post4 ⟩ ←
    ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec
  -- Bridge: i2 is also a cast, same as i and i1.
  have hi2_val : i2.val = x.val := by
    simp only [i2_post, IScalarTy.I8_numBits_eq, IScalarTy.I16_numBits_eq,
      Nat.reduceLeDiff, IScalar.val_mod_pow_greater_numBits]
  -- xabs.val = |x.val|: sign-mask trick `(x + xmask) XOR xmask = |x|`.
  -- Proof by case split on xmask.val ∈ {0, -1}. BitVec-level XOR identities
  -- are reduced via `BitVec.eq_of_toInt_eq` (no bv_decide needed).
  have hi3_val : i3.val = x.val + xmask.val := by rw [i3_post, hi2_val]
  have hxabs_val : xabs.val = x.val.natAbs := by
    have hxabs_bv_toInt : xabs.val = (i3.bv ^^^ xmask.bv).toInt := by
      change xabs.bv.toInt = _; fcongr 1
    rw [hxabs_bv_toInt]
    rcases xmask_post2 with hm | hm
    · -- xmask.val = -1, so x.val < 0, and xmask.bv = allOnes 16.
      have hx_neg : x.val < 0 := by rw [← hi1_val]; exact xmask_post3.mp hm
      have hxm_bv : xmask.bv = BitVec.allOnes 16 := by
        apply BitVec.eq_of_toInt_eq
        rw [BitVec.toInt_allOnes]
        change xmask.val = _
        rw [hm]; decide
      rw [hxm_bv, BitVec.xor_allOnes, BitVec.toInt_not]
      -- Goal: (↑(2^16 - 1 - i3.bv.toNat) : ℤ).bmod (2^16) = ↑x.val.natAbs.
      -- Bounds: i3.val = x.val - 1 ∈ [-9, -2].
      have hi3_toInt : i3.bv.toInt = x.val - 1 := by
        change i3.val = _; rw [hi3_val, hm]; ring
      have hi3_neg : i3.bv.toInt < 0 := by rw [hi3_toInt]; omega
      have hcond := BitVec.toInt_eq_toNat_cond i3.bv
      rw [hi3_toInt] at hcond
      split_ifs at hcond with hlt
      · exfalso; omega
      -- hcond : x.val - 1 = ↑i3.bv.toNat - 2^16
      have hi3_toNat : (i3.bv.toNat : ℤ) = x.val + (2^16 - 1) := by push_cast at hcond ⊢; omega
      have hbm_arg : (2^16 - 1 - (i3.bv.toNat : ℤ) : ℤ) = -x.val := by
        push_cast; omega
      rw [hbm_arg, Int.ofNat_natAbs_of_nonpos (le_of_lt hx_neg)]
      exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 15 (-x.val)
        (by omega) (by omega)
    · -- xmask.val = 0, so x.val ≥ 0, and xmask.bv = 0#16.
      have hx_nn : 0 ≤ x.val := by
        rw [← hi1_val]
        by_contra hneg
        push_neg at hneg
        have := xmask_post3.mpr hneg; omega
      have hxm_bv : xmask.bv = 0#16 := by
        apply BitVec.eq_of_toInt_eq
        change xmask.val = _
        rw [hm]; decide
      rw [hxm_bv, BitVec.xor_zero]
      change i3.val = _
      rw [hi3_val, hm, Int.natAbs_of_nonneg hx_nn]; ring
  let* ⟨ t1, t1_post1, t1_post2 ⟩ ← select_loop_spec
  · sorry
  · sorry
  let* ⟨ i4, i4_post1, i4_post2 ⟩ ← IScalar.and_spec
  let* ⟨ i5, i5_post ⟩ ← IScalar.hcast.step_spec
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
