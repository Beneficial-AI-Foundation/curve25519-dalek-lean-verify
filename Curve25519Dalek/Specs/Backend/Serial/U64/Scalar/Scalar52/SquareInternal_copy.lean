import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Tactics
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 500


/-! # SquareInternal

The main statement concerning `square_internal` is `square_internal_spec` (below).
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `square_internal` -/

/-- **Spec for `square_internal`**:
- Does not error and hence returns a result
- The result represents the square of the input field element
- Requires each limb to be less than 62 bits to prevent overflow
(The optimal bound on the limbs is 2^64 / √5  ≈ 2^62.839) -/
@[progress]
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a ∧
    (∀ i < 9, result[i]!.val < 2 ^ 127) := by
  unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  progress*
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    subst_vars; expand ha with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    unfold Array.make at *
    simp [Scalar52_wide_as_Nat, Scalar52_as_Nat, Finset.sum_range_succ, *]
    refine ⟨?_, ?_⟩
    · try grind
    · --
      intro i hi
      expand ha with 5
      interval_cases i
      all_goals
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        simp [*]
        simp only [Array.getElem!_Nat_eq] at *

        have h_len : a.val.length = 5 := List.Vector.length_val a

        have h_limbs (i : Nat) (hi : i < 5) : a[i].val < 2^62 := by
          have := ha i hi; norm_cast at this; rw [getElem!_pos] at this; exact this

      · -- subgoal 1
        let n0 := a[0].val
        have h0 : n0 < 2^62 := h_limbs 0 (by decide)

        calc
          n0 * n0 < 2^62 * 2^62 := by
            apply Nat.mul_lt_mul_of_le_of_lt
            · apply Nat.le_of_lt; exact h0
            · exact h0
            · decide
          _ = 2^124 := by norm_num
          _ < 2^127 := by norm_num

      · -- subgoal 2
        calc
          a[0].val * 2 * a[1].val
            = 2 * (a[0].val * a[1].val) := by ring
          _ < 2 * (2^62 * 2^62) := by
            apply Nat.mul_lt_mul_of_pos_left
            · apply Nat.mul_lt_mul_of_le_of_lt
              · exact Nat.le_of_lt (h_limbs 0 (by decide))
              · exact h_limbs 1 (by decide)
              · decide
            · decide -- 0 < 2
          _ = 2^125 := by norm_num
          _ < 2^127 := by norm_num

      · -- subgoal 3
        have h_part1 : a[0].val * 2 * a[2].val < 2^125 := by
          rw [Nat.mul_comm _ 2, Nat.mul_assoc]
          calc
            2 * (a[0].val * a[2].val)
              < 2 * (2^62 * 2^62) := by
                apply Nat.mul_lt_mul_of_pos_left
                · apply Nat.mul_lt_mul_of_le_of_lt
                  · apply Nat.le_of_lt; exact h_limbs 0 (by decide)
                  · exact h_limbs 2 (by decide)
                  · decide
                · decide
            _ = 2^125 := by norm_num

        have h_part2 : a[1].val * a[1].val < 2^124 := by
          calc
            a[1].val * a[1].val
              < 2^62 * 2^62 := by
                apply Nat.mul_lt_mul_of_le_of_lt
                · apply Nat.le_of_lt; exact h_limbs 1 (by decide)
                · exact h_limbs 1 (by decide)
                · decide
            _ = 2^124 := by norm_num

        calc
          _ < 2^125 + 2^124 := by apply Nat.add_lt_add h_part1 h_part2
          _ = 3 * 2^124     := by ring
          _ < 4 * 2^124     := by apply Nat.mul_lt_mul_of_pos_right <;> decide
          _ = 2^126         := by ring
          _ < 2^127         := by norm_num

      · -- subgoal 4
        have h_part1 : a[0].val * 2 * a[3].val < 2^125 := by
          rw [Nat.mul_comm _ 2, Nat.mul_assoc]
          calc
            2 * (a[0].val * a[3].val)
              < 2 * (2^62 * 2^62) := by
                apply Nat.mul_lt_mul_of_pos_left
                · apply Nat.mul_lt_mul_of_le_of_lt
                  · apply Nat.le_of_lt; exact h_limbs 0 (by decide)
                  · exact h_limbs 3 (by decide)
                  · decide
                · decide
            _ = 2^125 := by norm_num

        have h_part2 : a[1].val * 2 * a[2].val < 2^125 := by
          rw [Nat.mul_comm _ 2, Nat.mul_assoc]
          calc
            2 * (a[1].val * a[2].val)
              < 2 * (2^62 * 2^62) := by
                apply Nat.mul_lt_mul_of_pos_left
                · apply Nat.mul_lt_mul_of_le_of_lt
                  · apply Nat.le_of_lt; exact h_limbs 1 (by decide)
                  · exact h_limbs 2 (by decide)
                  · decide
                · decide
            _ = 2^125 := by norm_num

        calc
          _ < 2^125 + 2^125 := by apply Nat.add_lt_add h_part1 h_part2
          _ = 2 * 2^125     := by ring
          _ = 2^126         := by ring
          _ < 2^127         := by norm_num

      · -- subgoal 5
        have h_part1 : a[0].val * 2 * a[4].val < 2^125 := by
          rw [Nat.mul_comm _ 2, Nat.mul_assoc]
          calc
            2 * (a[0].val * a[4].val)
              < 2 * (2^62 * 2^62) := by
                apply Nat.mul_lt_mul_of_pos_left
                · apply Nat.mul_lt_mul_of_le_of_lt
                  · apply Nat.le_of_lt; exact h_limbs 0 (by decide)
                  · exact h_limbs 4 (by decide)
                  · decide
                · decide
            _ = 2^125 := by norm_num

        have h_part2 : a[1].val * 2 * a[3].val < 2^125 := by
          rw [Nat.mul_comm _ 2, Nat.mul_assoc]
          calc
            2 * (a[1].val * a[3].val)
              < 2 * (2^62 * 2^62) := by
                apply Nat.mul_lt_mul_of_pos_left
                · apply Nat.mul_lt_mul_of_le_of_lt
                  · apply Nat.le_of_lt; exact h_limbs 1 (by decide)
                  · exact h_limbs 3 (by decide)
                  · decide
                · decide
            _ = 2^125 := by norm_num

        have h_part3 : a[2].val * a[2].val < 2^124 := by
          calc
            a[2].val * a[2].val
              < 2^62 * 2^62 := by
                apply Nat.mul_lt_mul_of_le_of_lt
                · apply Nat.le_of_lt; exact h_limbs 2 (by decide)
                · exact h_limbs 2 (by decide)
                · decide
            _ = 2^124 := by norm_num

        try grind

      · -- subgoal 6
        let lemma_arith (n1 n4 n2 n3 : Nat)
          (h1 : n1 < 2^62) (h4 : n4 < 2^62) (h2 : n2 < 2^62) (h3 : n3 < 2^62) :
          n1 * 2 * n4 + n2 * 2 * n3 < 2^127 := by
            have h_term1 : n1 * 2 * n4 < 2^125 := by
              rw [Nat.mul_comm _ 2, Nat.mul_assoc]; calc
                2 * (n1 * n4) < 2 * (2^62 * 2^62) := by
                  apply Nat.mul_lt_mul_of_pos_left
                  · apply Nat.mul_lt_mul_of_le_of_lt
                    · apply Nat.le_of_lt; exact h1
                    · exact h4
                    · decide
                  · decide
                _ = 2^125 := by norm_num
            have h_term2 : n2 * 2 * n3 < 2^125 := by
              rw [Nat.mul_comm _ 2, Nat.mul_assoc]; calc
                2 * (n2 * n3) < 2 * (2^62 * 2^62) := by
                  apply Nat.mul_lt_mul_of_pos_left
                  · apply Nat.mul_lt_mul_of_le_of_lt
                    · apply Nat.le_of_lt; exact h2
                    · exact h3
                    · decide
                  · decide
                _ = 2^125 := by norm_num
            calc
              n1 * 2 * n4 + n2 * 2 * n3 < 2^125 + 2^125 := by apply Nat.add_lt_add h_term1 h_term2
              _ = 2^126 := by norm_num
              _ < 2^127 := by norm_num

        apply lemma_arith
        · exact h_limbs 3 (by decide)
        · exact h_limbs 1 (by decide)
        · exact h_limbs 4 (by decide)
        · exact h_limbs 2 (by decide)

      · -- subgoal 7
        let lemma_arith (n2 n4 n3 : Nat)
          (h2 : n2 < 2^62) (h4 : n4 < 2^62) (h3 : n3 < 2^62) :
          n2 * 2 * n4 + n3 * n3 < 2^127 := by
            have h_term1 : n2 * 2 * n4 < 2^125 := by
              rw [Nat.mul_comm _ 2, Nat.mul_assoc]
              calc
                2 * (n2 * n4) < 2 * (2^62 * 2^62) := by
                  apply Nat.mul_lt_mul_of_pos_left
                  · apply Nat.mul_lt_mul_of_le_of_lt
                    · apply Nat.le_of_lt; exact h2
                    · exact h4
                    · decide
                  · decide
                _ = 2^125 := by norm_num

            have h_term2 : n3 * n3 < 2^124 := by
              calc
                n3 * n3 < 2^62 * 2^62 := by
                  apply Nat.mul_lt_mul_of_le_of_lt
                  · apply Nat.le_of_lt; exact h3
                  · exact h3
                  · decide
                _ = 2^124 := by norm_num

            calc
              n2 * 2 * n4 + n3 * n3 < 2^125 + 2^124 := by apply Nat.add_lt_add h_term1 h_term2
              _ = 3 * 2^124 := by ring
              _ < 4 * 2^124 := by apply Nat.mul_lt_mul_of_pos_right <;> decide
              _ = 2^126     := by ring
              _ < 2^127     := by norm_num

        apply lemma_arith
        · exact h_limbs 3 (by decide)
        · exact h_limbs 2 (by decide)
        · exact h_limbs 4 (by decide)

      · -- subgoal 8
        let n3 := a[3].val
        let n4 := a[4].val
        have h3 : n3 < 2^62 := h_limbs 3 (by decide)
        have h4 : n4 < 2^62 := h_limbs 4 (by decide)

        rw [Nat.mul_comm _ 2, Nat.mul_assoc]
        calc
          2 * (n3 * n4)
            < 2 * (2^62 * 2^62) := by
              apply Nat.mul_lt_mul_of_pos_left
              · apply Nat.mul_lt_mul_of_le_of_lt
                · apply Nat.le_of_lt; exact h3
                · exact h4
                · decide
              · decide
          _ = 2^125 := by norm_num
          _ < 2^127 := by norm_num

      · -- subgoal 9
        let n4 := a[4].val
        have h4 : n4 < 2^62 := h_limbs 4 (by decide)

        calc
          n4 * n4 < 2^62 * 2^62 := by
            apply Nat.mul_lt_mul_of_le_of_lt
            · apply Nat.le_of_lt; exact h4
            · exact h4
            · decide
          _ = 2^124 := by norm_num
          _ < 2^127 := by norm_num
    -- END TASK



end curve25519_dalek.backend.serial.u64.scalar.Scalar52
