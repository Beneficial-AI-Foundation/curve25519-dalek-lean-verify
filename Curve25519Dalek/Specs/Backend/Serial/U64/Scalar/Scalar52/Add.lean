/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang, Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Mathlib.Data.Nat.ModEq


/-! # Spec Theorem for `Scalar52::add`

Specification and proof for `Scalar52::add`.

This function adds two elements.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

set_option exponentiation.threshold 280

attribute [-simp] Int.reducePow Nat.reducePow

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

private theorem next_spec (range : core.ops.range.Range Usize) :
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

/-
natural language description:

    • Takes two input unpacked scalars u and u' and returns an unpacked scalar v representing
      the sum (u + u') mod L where L is the group order.

natural language specs:

    • scalar_to_nat(v) = (scalar_to_nat(u) + scalar_to_nat(u')) mod L
-/

/- **Spec for `backend.serial.u64.scalar.Scalar52.add_loop`**:
- Starting from index `i` with accumulator `sum` and carry `carry`
- Computes limb-wise addition with carry propagation
- Result limbs are bounded by 2^52
- Parts of sum before index i are preserved
- The result satisfies the modular arithmetic property -/
@[step]
theorem add_loop_spec (a b sum : Scalar52) (mask carry : U64) (i : Usize)
    (ha : ∀ j < 5, a[j]!.val < 2 ^ 52) (hb : ∀ j < 5, b[j]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < 2 ^ 259) (hb' : Scalar52_as_Nat b < 2 ^ 259)
    (hmask : mask.val = 2 ^ 52 - 1) (hi : i.val ≤ 5)
    (hcarry : i.val = 5 → carry.val < 2 ^ 52)
    (hcarry' : ∀ i < 5, carry.val < 2 ^ 53)
    (hsum : ∀ j < 5, sum[j]!.val < 2 ^ 52)
    (hsum' : ∀ j < 5, i.val ≤ j → sum[j]!.val = 0) :
    add_loop { start := i, «end» := 5#usize } a b sum mask carry ⦃ (sum' : Scalar52) =>
      (∀ j < 5, sum'[j]!.val < 2 ^ 52) ∧
      (∀ j < i.val, sum'[j]!.val = sum[j]!.val) ∧
      ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * sum'[j]!.val =
        ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * (a[j]!.val + b[j]!.val) +
        2 ^ (52 * i.val) * (carry.val / 2 ^ 52) ⦄ := by
  unfold add_loop
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  obtain ⟨o, iter1, h_next, h_none_branch, h_some_branch⟩ := next_spec
    { start := i, «end» := 5#usize }
  rw [h_next, bind_tc_ok]
  simp only [Prod.mk.eta, bind_assoc, bind_tc_ok, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD]
  match o with
  | none =>
    -- Base case: range exhausted, i = 5
    have hi5 : i.val = 5 := by
      have : ¬ i.val < 5 := by
        intro hlt
        obtain ⟨h_eq, _, _⟩ := h_some_branch hlt
        exact absurd h_eq (by simp)
      omega
    refine ⟨hsum, fun j _ => rfl, ?_⟩
    simp only [hi5, le_refl, Finset.Ico_eq_empty_of_le, Finset.sum_empty, Nat.reduceMul,
      zero_add, zero_eq_mul, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true,
      and_true, Nat.div_eq_zero_iff, false_or]; agrind
  | some val =>
    simp only
    step*
    · -- Overflow check for carry1 (i3 + i4 ≤ U64.max)
      have : carry.val >>> 52 ≤ 1 := by have := hcarry' i (by agrind); omega
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
        UScalar.ofNatCore_val_eq, UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv] at *; agrind
    rename_i y y1
    -- Recursive WP obligation: apply IH (add_loop_spec) and transfer postcondition
    -- Establish facts about iter1 from h_some_branch
    have h_lt : i.val < 5 := by agrind
    obtain ⟨h_o_eq, h_start_val, h_end_eq⟩ := h_some_branch h_lt
    -- iter1.start.val = val.val + 1, iter1.end = 5#usize
    -- Preconditions for the IH
    have hi1 : iter1.start.val ≤ 5 := by grind
    have hcarry1 : iter1.start.val = 5 → carry1.val < 2 ^ 52 := by
      intro hi5
      have : val.val = 4 := by grind
      have : a[4]!.val < 2 ^ 51 := by agrind [Scalar52_top_limb_lt_of_as_Nat_lt]
      have : b[4]!.val < 2 ^ 51 := by agrind [Scalar52_top_limb_lt_of_as_Nat_lt]
      have : carry.val >>> 52 ≤ 1 := by have := hcarry' val (by agrind); omega
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
        UScalar.ofNatCore_val_eq, UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, UScalar.val_and,
        List.Vector.length_val, Nat.lt_add_one, getElem!_pos, gt_iff_lt] at *; grind
    have hcarry1' : ∀ j < 5, carry1.val < 2 ^ 53 := by
      intro j hj
      have : carry.val >>> 52 ≤ 1 := by have := hcarry' val (by agrind); omega
      have := ha val (by agrind)
      have := hb val (by agrind)
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
        UScalar.ofNatCore_val_eq, UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, UScalar.val_and,
        gt_iff_lt] at *; agrind
    have hsum1 : ∀ j < 5, (y i5)[j]!.val < 2 ^ 52 := by
      intro j hj
      by_cases hc : j = val
      · rw [hc]
        have := Array.set_of_eq sum i5 val (by agrind)
        simp only [Array.getElem!_Nat_eq, Array.set_val_eq, gt_iff_lt] at this ⊢
        simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
          getElem!_pos, List.getElem!_eq_getElem?_getD, UScalarTy.U64_numBits_eq,
          Bvify.U64.UScalar_bv, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod,
          UScalar.ofNat_self_val, Array.set_val_eq, List.length_set, List.getElem_set_self,
          getElem?_pos, Option.getD_some]
        agrind
      · have := Array.set_of_ne sum i5 j val (by agrind) (by agrind) (by agrind)
        have := hsum j (by agrind)
        simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
          getElem!_pos, List.getElem!_eq_getElem?_getD, UScalarTy.U64_numBits_eq,
          Bvify.U64.UScalar_bv, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod,
          UScalar.ofNat_self_val, Array.set_val_eq, List.length_set, gt_iff_lt]; agrind
    have hsum'1 : ∀ j < 5, iter1.start.val ≤ j → (y i5)[j]!.val = 0 := by
      intro j hj hjge
      have hne : j ≠ val := by agrind
      have := Array.set_of_ne' sum i5 j val (by agrind) (by omega)
      have := hsum' j hj (by grind)
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        getElem!_pos,  UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv,
        UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod, Order.add_one_le_iff, ne_eq,
        Array.set_val_eq, List.length_set]; agrind
    -- Rewrite iter1 to match the form expected by add_loop_spec
    have h_iter1_eq : iter1 = { start := iter1.start, «end» := 5#usize } := by
      rcases iter1 with ⟨s, e⟩
      simp only [core.ops.range.Range.mk.injEq, true_and]
      grind only
    rw [h_iter1_eq]
    -- Apply the IH with all preconditions
    apply spec_mono (add_loop_spec a b (y i5) mask carry1 iter1.start ha hb ha' hb' hmask
        hi1 hcarry1 hcarry1' hsum1 hsum'1)
    -- Transfer postcondition
    intro sum'' ⟨hQ1, hQ2, hQ3⟩
    refine ⟨hQ1, ?_, ?_⟩
    · -- ∀ j < val.val, sum''[j]!.val = sum[j]!.val
      intro j hj
      have h1 := hQ2 j (by grind)
      rw [x_post1] at h1
      have h2 := congrArg UScalar.val (Array.set_of_ne' sum i5 j val (by agrind) (by grind))
      rw [Array.getElem_eq_getElem! sum j (by agrind)] at h2
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Array.set_val_eq] at h1 h2
      rw[h1, h2]
    · -- Sum equality
      have hc1val : carry1.val = a[val]!.val + b[val]!.val + carry.val / 2 ^ 52 := by
        set_option maxRecDepth 1000 in
        simp only [List.getElem!_eq_getElem?_getD, Array.getElem!_Usize_eq,
          carry1_post, i3_post, i1_post, i2_post, i4_post1]; omega
      have hsum''i : sum''[val]!.val = carry1.val % 2 ^ 52 := by
        have h1 := hQ2 val.val (by grind)
        -- h1: sum''[val.val]!.val = (y i5)[val.val]!.val
        have h2 := Array.set_of_eq sum i5 val (by grind only [usr Subtype.property])
        -- h2: (sum.set val#usize i5)[val.val]! = i5
        have h3 : i5.val = carry1.val % 2 ^ 52 := by
          have hmod := Nat.and_two_pow_sub_one_eq_mod carry1.val 52
          simp only [UScalar.val_and, hmask] at *
          omega
        simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Array.set_val_eq] at h1 h2
        simp only [Array.getElem!_Usize_eq, List.getElem!_eq_getElem?_getD]
        rw[h1, x_post1 ]
        clear *- h2 h3
        grind
      have hfin : ∑ j ∈ Finset.Ico (i.val + 1) 5, 2 ^ (52 * j) * sum''[j]!.val =
          ∑ j ∈ Finset.Ico (i.val + 1) 5, 2 ^ (52 * j) * (a[j]!.val + b[j]!.val) +
          2 ^ (52 * (i.val + 1)) * (carry1.val / 2 ^ 52) := by
        have h52 : 4503599627370496 = 2 ^ 52 := by agrind
        simp only at h_start_val
        rw [h_start_val] at hQ3
        exact hQ3
      have hpow : 2 ^ (52 * i.val) * (carry1.val % 2 ^ 52) +
          2 ^ (52 * (i.val + 1)) * (carry1.val / 2 ^ 52) = 2 ^ (52 * i.val) * carry1.val := by
        have : carry1.val % 2 ^ 52 + 2 ^ 52 * (carry1.val / 2 ^ 52) = carry1.val := by agrind
        agrind
      calc ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * sum''[j]!.val
        _ = 2 ^ (52 * i.val) * sum''[i]!.val +
            ∑ j ∈ Finset.Ico (i.val + 1) 5, 2 ^ (52 * j) * sum''[j]!.val := by
          have hlt : i.val < 5 := by agrind
          simp [Finset.sum_eq_sum_Ico_succ_bot hlt]
        _ = ∑ j ∈ Finset.Ico (i.val) 5, 2 ^ (52 * j) * (a[j]!.val + b[j]!.val) +
            2 ^ (52 * i.val) * (carry.val / 2 ^ 52) := by
          have hlt : i.val < 5 := by agrind
          rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
          agrind
    termination_by 5 - i.val
    decreasing_by
      simp only at h_start_val
      rw[h_start_val]
      grind

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- Requires the input values to be bounded by  2 ^ 259
- The result represents the sum of the two input scalars modulo L
-/
@[step]
theorem add_spec (a b : Scalar52)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < L) (hb' : Scalar52_as_Nat b ≤ L) :
    add a b ⦃ (v : Scalar52) =>
      Scalar52_as_Nat v ≡ Scalar52_as_Nat a + Scalar52_as_Nat b [MOD L] ∧
      Scalar52_as_Nat v < L ∧ ∀ i < 5, v[i]!.val < 2 ^ 52 ⦄ := by
  unfold add
  step*
  · have : L < 2 ^ 259 := by unfold L; agrind
    agrind
  · have : L < 2 ^ 259 := by unfold L; agrind
    agrind
  · intro j _
    unfold ZERO
    interval_cases j <;> decide
  · unfold ZERO; decide
  · intro i hi
    unfold constants.L
    interval_cases i <;> decide
  · rw [constants.L_spec]
    have : Scalar52_as_Nat sum = Scalar52_as_Nat a + Scalar52_as_Nat b := calc
      ∑ i ∈ Finset.Ico 0 5, 2 ^ (52 * i) * sum[i]!.val
      _ = ∑ i ∈ Finset.Ico 0 5, 2 ^ (52 * i) * (a[i]!.val + b[i]!.val) := by assumption
      _ = ∑ i ∈ Finset.Ico 0 5, (2 ^ (52 * i) * a[i]!.val + 2 ^ (52 * i) * b[i]!.val) := by grind
      _ = _ := by simp [Scalar52_as_Nat, Finset.sum_add_distrib]
    omega
  · agrind [constants.L_spec]
  · refine ⟨?_, by assumption, by assumption⟩
    rw [constants.L_spec] at *
    have h1 : Scalar52_as_Nat v ≡ Scalar52_as_Nat sum [MOD L] := by
      have hL_mod : L ≡ 0 [MOD L] := by
        rw [Nat.ModEq, Nat.zero_mod, Nat.mod_self]
      have : Scalar52_as_Nat v + L ≡ Scalar52_as_Nat v + 0 [MOD L] :=
        Nat.ModEq.add_left _ hL_mod
      simp only [add_zero] at this
      exact this.symm.trans v_post1
    have h2 : Scalar52_as_Nat sum = Scalar52_as_Nat a + Scalar52_as_Nat b := by
      unfold Scalar52_as_Nat
      simp only [Finset.range_eq_Ico] at v_post3 ⊢
      conv_lhs => rw [sum_post3]
      simp [Finset.sum_add_distrib, Nat.mul_add]
    agrind

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
