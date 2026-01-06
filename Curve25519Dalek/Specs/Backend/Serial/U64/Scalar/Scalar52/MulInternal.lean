import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Defs
import Curve25519Dalek.Tactics
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000 -- scalr_tac exceeds standard heartbeats rates
set_option exponentiation.threshold 500

/-! # MulInternal

The main statement concerning `mul_internal` is `mul_internal_spec` (below).
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `mul_internal` -/

/-- **Spec for `backend.serial.u64.scalar.Scalar52.mul_internal`**:
- Does not error and hence returns a result
- The result represents the product of the two input field elements
- Requires that each input limb is at most 62 bits to prevent overflow -/
@[progress]
theorem mul_internal_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62) :
    ∃ result, mul_internal a b = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat b ∧
    (∀ i < 9, result[i]!.val < 2 ^ 127) := by
  unfold mul_internal
  unfold backend.serial.u64.scalar.IndexScalar52UsizeU64.index
  progress*
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand ha with 5; expand hb with 5; simp [*]; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp [*, Scalar52_wide_as_Nat, Scalar52_as_Nat, Finset.sum_range_succ]
    refine ⟨?_,?_⟩
    · -- Main equation
      try grind
    · -- Post condition
      intro i hi
      expand ha with 5
      expand hb with 5

      interval_cases i
      · -- subgoal 1
        simp only [Nat.not_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, OfNat.zero_ne_ofNat,
          not_lt_zero', Nat.ofNat_pos, or_true, or_self, List.getElem!_set_ne, one_ne_zero,
          zero_ne_one, zero_lt_one, List.Vector.length_val, UScalar.ofNat_val_eq, List.getElem!_set,
          gt_iff_lt]
        simp only [*]
        try scalar_tac
      · -- subgoal 2
        simp only [Nat.not_eq, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, OfNat.one_ne_ofNat,
          Nat.not_ofNat_lt_one, Nat.one_lt_ofNat, or_true, or_self, List.getElem!_set_ne,
          List.length_set, List.Vector.length_val, UScalar.ofNat_val_eq, List.getElem!_set,
          gt_iff_lt]
        simp only [*]
        try scalar_tac
      · -- subgoal 3
        simp only [Nat.not_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Nat.reduceLT, or_true,
          or_self, List.getElem!_set_ne, Nat.succ_ne_self, Nat.lt_add_one, List.length_set,
          List.Vector.length_val, UScalar.ofNat_val_eq, List.getElem!_set, gt_iff_lt]
        simp only [*]
        try scalar_tac
      · -- subgoal 4
        simp only [Nat.not_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Nat.reduceLT, or_true,
          or_self, List.getElem!_set_ne, Nat.succ_ne_self, Nat.lt_add_one, List.length_set,
          List.Vector.length_val, UScalar.ofNat_val_eq, List.getElem!_set, gt_iff_lt]
        simp only [*]
        try scalar_tac
      · -- subgoal 5
        simp only [Nat.not_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Nat.reduceLT, or_true,
          or_self, List.getElem!_set_ne, Nat.succ_ne_self, Nat.lt_add_one, List.length_set,
          List.Vector.length_val, UScalar.ofNat_val_eq, List.getElem!_set, gt_iff_lt]
        simp only [*]
        try scalar_tac
      · -- subgoal 6
        simp only [Nat.not_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Nat.reduceLT, or_true,
          or_self, List.getElem!_set_ne, Nat.succ_ne_self, Nat.lt_add_one, List.length_set,
          List.Vector.length_val, UScalar.ofNat_val_eq, List.getElem!_set, gt_iff_lt]
        simp only [*]
        try scalar_tac
      · -- subgoal 7
        simp only [Nat.not_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Nat.reduceLT, or_true,
          or_self, List.getElem!_set_ne, Nat.succ_ne_self, Nat.lt_add_one, List.length_set,
          List.Vector.length_val, UScalar.ofNat_val_eq, List.getElem!_set, gt_iff_lt]
        simp only [*]
        try scalar_tac
      · -- subgoal 8
        simp only [Nat.not_eq, ne_eq, Nat.succ_ne_self, not_false_eq_true, Nat.reduceEqDiff,
          Nat.reduceLT, Nat.lt_add_one, or_true, or_self, List.getElem!_set_ne, List.length_set,
          List.Vector.length_val, UScalar.ofNat_val_eq, List.getElem!_set, gt_iff_lt]
        simp only [*]
        try scalar_tac
      · -- subgoal 9
        simp only [List.length_set, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.lt_add_one,
          List.getElem!_set, gt_iff_lt]
        simp only [*]
        try scalar_tac
    -- END TASK



end curve25519_dalek.backend.serial.u64.scalar.Scalar52
