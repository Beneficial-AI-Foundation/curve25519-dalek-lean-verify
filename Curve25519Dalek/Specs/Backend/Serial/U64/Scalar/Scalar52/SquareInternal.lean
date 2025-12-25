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

namespace Calc

/-- Helper: x * y < 2^124 -/
theorem mul {x y : Nat} (hx : x < 2 ^ 62) (hy : y < 2 ^ 62) :
    x * y < 2^124 := by
  calc
    x * y < 2^62 * 2^62 := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hx) hy (by decide)
    _ = 2^124 := by norm_num

/-- Helper: x * x < 2^124 (Special case for squares) -/
theorem sq {x : Nat} (hx : x < 2 ^ 62) : x * x < 2^124 := mul hx hx

/-- Helper: 2 * x * y < 2^125 -/
theorem mul2 {x y : Nat} (hx : x < 2 ^ 62) (hy : y < 2 ^ 62) :
    2 * x * y < 2^125 := by
  rw [Nat.mul_assoc]
  calc
    2 * (x * y) < 2 * 2^124 := by
      apply Nat.mul_lt_mul_of_pos_left
      · exact mul hx hy
      · decide
    _ = 2^125 := by norm_num

/-- Helper: a + b < 2^127 -/
theorem add {a b : Nat} (ha : a < 2 ^ 126) (hb : b < 2 ^ 126) :
    a + b < 2^127 := by
  calc
    a + b < 2^126 + 2^126 := Nat.add_lt_add ha hb
    _ = 2 * 2^126 := by ring
    _ = 2^127 := by norm_num

end Calc

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
    simp only [Scalar52_wide_as_Nat, Scalar52_as_Nat, Finset.sum_range_succ, *]
    refine ⟨?_, ?_⟩
    · --
      try grind
      
      sorry
    · -- Postcondition Logic
      sorry

    --   intro i hi

    --   let n (k : Nat) : Nat := a[k]!.val
    --   have hn (k : Nat) (hk : k < 5) : n k < 2^62 := by
    --     dsimp [n]; have := ha k hk; norm_cast at this
    --     rw [List.getElem!_pos] at this <;> simp [*, List.Vector.length_val a]
    --     exact this

    --   norm_cast
    --   expand ha with 5
    --   interval_cases i

    --   -- 1. n0 * n0
    --   · apply Nat.lt_trans (Calc.sq (hn 0 (by decide))); norm_num

    --   -- 2. 2 * n0 * n1
    --   · apply Nat.lt_trans (Calc.mul2 (hn 0 (by decide)) (hn 1 (by decide))); norm_num

    --   -- 3. 2*n0*n2 + n1*n1
    --   · apply Calc.add
    --     · apply Nat.lt_trans (Calc.mul2 (hn 0 (by decide)) (hn 2 (by decide))); norm_num
    --     · apply Nat.lt_trans (Calc.sq (hn 1 (by decide))); norm_num

    --   -- 4. 2*n0*n3 + 2*n1*n2
    --   · apply Calc.add
    --     · apply Nat.lt_trans (Calc.mul2 (hn 0 (by decide)) (hn 3 (by decide))); norm_num
    --     · apply Nat.lt_trans (Calc.mul2 (hn 1 (by decide)) (hn 2 (by decide))); norm_num

    --   -- 5. 2*n0*n4 + 2*n1*n3 + n2*n2
    --   · apply Nat.lt_trans _ (show 2^126 + 2^124 < 2^127 by norm_num)
    --     apply Nat.add_lt_add
    --     · apply Calc.add -- recursive add for the first two
    --       · apply Nat.lt_trans (Calc.mul2 (hn 0 (by decide)) (hn 4 (by decide))); norm_num
    --       · apply Nat.lt_trans (Calc.mul2 (hn 1 (by decide)) (hn 3 (by decide))); norm_num
    --     · apply Nat.lt_trans (Calc.sq (hn 2 (by decide))); norm_num

    --   -- 6. 2*n1*n4 + 2*n2*n3
    --   · apply Calc.add
    --     · apply Nat.lt_trans (Calc.mul2 (hn 1 (by decide)) (hn 4 (by decide))); norm_num
    --     · apply Nat.lt_trans (Calc.mul2 (hn 2 (by decide)) (hn 3 (by decide))); norm_num

    --   -- 7. 2*n2*n4 + n3*n3
    --   · apply Calc.add
    --     · apply Nat.lt_trans (Calc.mul2 (hn 2 (by decide)) (hn 4 (by decide))); norm_num
    --     · apply Nat.lt_trans (Calc.sq (hn 3 (by decide))); norm_num

    --   -- 8. 2*n3*n4
    --   · apply Nat.lt_trans (Calc.mul2 (hn 3 (by decide)) (hn 4 (by decide))); norm_num

    --   -- 9. n4*n4
    --   · apply Nat.lt_trans (Calc.sq (hn 4 (by decide))); norm_num
    -- -- END TASK



end curve25519_dalek.backend.serial.u64.scalar.Scalar52
