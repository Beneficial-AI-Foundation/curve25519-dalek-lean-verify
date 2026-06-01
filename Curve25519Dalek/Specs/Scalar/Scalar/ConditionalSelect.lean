/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::conditional_select`

Implements the `ConditionallySelectable` trait for `Scalar` via element-wise constant-time
byte selection, conditionally returning one of two scalars based on a `Choice` value.

• Takes two `Scalar`s `a` and `b` and a `Choice` value
• Creates a new 32-byte array initialized to zeros
• For each index `i` in `0..32`, sets `bytes[i]` to
  `U8::conditional_select(a.bytes[i], b.bytes[i], choice)`
• Returns a `Scalar` with the resulting bytes array
• Returns `b` when `choice = Choice.one` (`choice.val = 1`) and `a` when
  `choice = Choice.zero` (`choice.val = 0`), in constant time

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable

theorem next_spec (range : core.ops.range.Range Usize) :
    ∃ opt range',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range = ok (opt, range') ∧
      (¬ range.start.val < range.end.val → opt = none ∧ range' = range) ∧
      (range.start.val < range.end.val →
          opt = some range.start ∧
          range'.start.val = range.start.val + 1 ∧
          range'.end = range.end) := by
  simp only [core.iter.range.IteratorRange.next]
  simp only [liftFun2, liftFun1, core.clone.impls.CloneUsize.clone, bind_tc_ok, not_lt]
  have h_lt_iff :
      (core.cmp.impls.PartialOrdUsize.lt range.start range.end = true) =
      (range.start.val < range.end.val) := by
    simp [core.cmp.impls.PartialOrdUsize.lt]
  simp only [h_lt_iff]
  by_cases hlt : range.start.val < range.end.val
  · rw [if_pos hlt]
    have hbound : range.start.val + 1 ≤ Usize.max := by
      have := range.end.hBounds; scalar_tac
    refine ⟨some range.start, {range with start := ⟨range.start.val + 1, by scalar_tac⟩},
            ?_, ?_, ?_⟩
    · simp only [core.iter.range.StepUsize.forward_checked, bind_tc_ok]
      have hca := Usize.checked_add_bv_spec range.start 1#usize
      rcases heq : Usize.checked_add range.start 1#usize with _ | z
      · rw [heq] at hca; scalar_tac
      · simp only
        rw [heq] at hca
        obtain ⟨_, hval, _⟩ := hca
        have hzval : z.val = range.start.val + 1 := by scalar_tac
        congr 4
        exact UScalar.eq_of_val_eq hzval
    · intro h; omega
    · intro _; exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hlt]
    exact ⟨none, range, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h hlt⟩

/-- **Spec theorem for `Array.update`** (specialised to `Array U8 32`)
• The update always succeeds (no panic) for in-bounds index `j` (given `j.val < 32`)
• All elements at indices `k ≠ j.val` are unchanged in the result: `arr'[k]! = arr[k]!`
• The element at index `j.val` equals the new value `v` in the result: `arr'[j.val]! = v`
-/
@[step]
private lemma Array_U8_32_update_spec (arr : Array U8 32#usize) (j : Usize)
    (v : U8) (hj : j.val < 32) :
    Array.update arr j v ⦃ (arr' : Array U8 32#usize) =>
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

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::conditional_select_loop`**
• The loop always succeeds (no panic) given valid range bounds and loop invariant
• For all `j < 32`, `result[j]!` = `b.bytes[j]!` if `choice.val = 1`, and `a.bytes[j]!` otherwise
-/
@[step]
theorem conditional_select_loop_spec
    (iter : core.ops.range.Range Usize) (a b : scalar.Scalar)
    (choice : subtle.Choice) (bytes : Array U8 32#usize)
    (hend : iter.end = 32#usize)
    (hstart : iter.start ≤ 32#usize)
    (hinv : ∀ j : Nat, j < iter.start.val →
      bytes[j]! = (if choice.val = 1#u8 then b else a).bytes[j]!) :
    conditional_select_loop iter a b choice bytes ⦃ (result : Array U8 32#usize) =>
      ∀ j : Nat, j < 32 →
        result[j]! = (if choice.val = 1#u8 then b else a).bytes[j]! ⦄ := by
  unfold conditional_select_loop
  obtain ⟨o, iter1, h_next, h_none_branch, h_some_branch⟩ := next_spec iter
  rw [h_next, bind_tc_ok]
  match o with
  | none =>
    have hge : ¬ iter.start.val < iter.end.val := by
      intro hlt
      exact absurd (h_some_branch hlt).1 (by simp)
    have hend32 : iter.end.val = 32 := by simp [hend]
    intro j hj
    apply hinv
    scalar_tac
  | some i =>
    have hlt : iter.start.val < iter.end.val := by
      by_contra hge
      exact absurd (h_none_branch hge).1 (by simp)
    obtain ⟨hi_eq_some, hiter1_start, hiter1_end⟩ := h_some_branch hlt
    have hi_val : i.val = iter.start.val := by
      have h : some i = some iter.start := hi_eq_some
      exact congrArg UScalar.val (Option.some.inj h)
    have hend32 : iter.end.val = 32 := by simp [hend]
    have hi_lt32 : i.val < 32 := by omega
    step as ⟨ai, hai⟩
    step as ⟨bi, hbi⟩
    step as ⟨ci, hci⟩
    step with Array_U8_32_update_spec bytes i ci hi_lt32
      as ⟨bytes', hbytes'_other, hbytes'_curr⟩
    apply spec_mono
      (conditional_select_loop_spec iter1 a b choice bytes'
        (by rw [hiter1_end]; exact hend)
        (by scalar_tac)
        (by
          intro j hj_lt
          rw [hiter1_start] at hj_lt
          by_cases hje : j = i.val
          · subst hje
            rw [hbytes'_curr, hci]
            split_ifs with h
            · simp only [Array.getElem!_Nat_eq]
              exact hbi
            · simp only [Array.getElem!_Nat_eq]
              exact hai
          · rw [hbytes'_other j hje]
            apply hinv
            omega))
    intro result hresult
    exact hresult
  termination_by iter.end.val - iter.start.val
  decreasing_by
    rw [hiter1_start]
    grind

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::conditional_select`**
• The function always succeeds (no panic) for any input `Scalar`s and `Choice`
• Returns `b` when `choice.val = 1` and `a` when `choice.val = 0`
-/
@[step]
theorem conditional_select_spec
    (a b : scalar.Scalar)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : scalar.Scalar) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by
  unfold conditional_select
  step as ⟨bytes1, hbytes1⟩
  have arr_ext : ∀ (x y : Array U8 32#usize),
      (∀ i < 32, x[i]! = y[i]!) → x = y := by
    intro x y h
    apply Subtype.ext
    rw [List.eq_iff_forall_eq_getElem!]
    exact ⟨by simp only [List.Vector.length_val], fun i hi => by
      simp only [List.getElem!_eq_getElem?_getD]
      exact h i (by scalar_tac)⟩
  by_cases h : choice.val = 1#u8
  all_goals simp only [h, ite_true, ite_false] at *
  all_goals obtain ⟨_⟩ := a
  all_goals obtain ⟨_⟩ := b
  all_goals simp only [scalar.Scalar.mk.injEq]
  all_goals exact arr_ext _ _ hbytes1

end curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable
