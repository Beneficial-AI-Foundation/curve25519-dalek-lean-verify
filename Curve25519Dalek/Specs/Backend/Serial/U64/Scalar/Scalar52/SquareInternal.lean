import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Tactics
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 500


/-! # SquareInternal

The main statement concerning `square_internal` is `square_internal_spec` (below).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

attribute [-simp] Int.reducePow Nat.reducePow

/-- Helper: x * y < 2^124 -/
private theorem bounds_mul {x y : Nat} (hx : x < 2 ^ 62) (hy : y < 2 ^ 62) :
    x * y < 2^124 := by
  calc
    x * y < 2^62 * 2^62 := Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hx) hy (by decide)
    _ = 2^124 := by norm_num

/-- Helper: x * x < 2^124 (Special case for squares) -/
private theorem bounds_sq {x : Nat} (hx : x < 2 ^ 62) : x * x < 2^124 := bounds_mul hx hx

/-- Helper: 2 * x * y < 2^125 -/
private theorem bounds_mul2 {x y : Nat} (hx : x < 2 ^ 62) (hy : y < 2 ^ 62) :
    2 * x * y < 2^125 := by
  rw [Nat.mul_assoc]
  calc
    2 * (x * y) < 2 * 2^124 := by
      apply Nat.mul_lt_mul_of_pos_left
      · exact bounds_mul hx hy
      · decide
    _ = 2^125 := by norm_num

/-- Helper: a + b < 2^127 -/
private theorem bounds_add {a b : Nat} (ha : a < 2 ^ 126) (hb : b < 2 ^ 126) :
    a + b < 2^127 := by
  calc
    a + b < 2^126 + 2^126 := Nat.add_lt_add ha hb
    _ = 2 * 2^126 := by ring
    _ = 2^127 := by norm_num


/-! ## Spec for `square_internal` -/

/-
Square_internal computes `a^2` using 52-bit limb optimizations.

Corresponds to the Rust function `Scalar52::square_internal` defined
in `curve25519-dalek/src/backend/serial/u64/scalar.rs`.
-/

/-- **Spec for `square_internal`**:
- Does not error and hence returns a result
- The result represents the square of the input field element
- Requires each limb to be less than 62 bits to prevent overflow
(The optimal bound on the limbs is 2^64 / √5  ≈ 2^62.839) -/
@[progress]
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    square_internal a ⦃ result =>
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a ∧
    (∀ i < 9, result[i]!.val < 2 ^ 127) ⦄ := by
  unfold square_internal backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  progress*

  all_goals try (subst_vars; expand ha with 5; scalar_tac)

  · -- Main Proof
    unfold Array.make at *
    simp [Scalar52_wide_as_Nat, Scalar52_as_Nat, Finset.sum_range_succ, *]
    refine ⟨?_, ?_⟩
    · try grind
    · -- Postcondition Logic
      intro i hi
      expand ha with 5
      interval_cases i

      all_goals
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        simp [*]
        simp only [Array.getElem!_Nat_eq] at *
        try repeat rw [← getElem!_pos]
        try rw [Nat.mul_comm _ 2]

      · -- 1. a0 * a0
        apply Nat.lt_trans (bounds_sq ha_0); norm_num

      · -- 2. 2 * a0 * a1
        apply Nat.lt_trans (bounds_mul2 ha_0 ha_1)
        norm_num

      · -- 3. 2 * a0 * a2 + a1 * a1
        apply bounds_add
        · apply Nat.lt_trans (bounds_mul2 ha_0 ha_2); norm_num
        · apply Nat.lt_trans (bounds_sq ha_1); norm_num

      · -- 4. 2 * a0 * a3 + 2 * a1 * a2
        apply bounds_add
        · apply Nat.lt_trans (bounds_mul2 ha_0 ha_3); norm_num
        · rw [Nat.mul_comm _ 2]; apply Nat.lt_trans (bounds_mul2 ha_1 ha_2); norm_num

      · -- 5. 2 * a0 * a4 + 2 * a1 * a3 + a2 * a2
        apply bounds_add
        · apply Nat.add_lt_add
          · apply bounds_mul2 ha_0 ha_4
          · rw [Nat.mul_comm _ 2]
            apply bounds_mul2 ha_1 ha_3
        · apply Nat.lt_trans (bounds_sq ha_2)
          norm_num

      · -- 6. 2 * a1 * a4 + 2 * a2 * a3
        apply bounds_add
        · apply Nat.lt_trans (bounds_mul2 ha_1 ha_4); norm_num
        · rw [Nat.mul_comm _ 2]; apply Nat.lt_trans (bounds_mul2 ha_2 ha_3); norm_num

      · -- 7. 2 * a2 * a4 + a3 * a3
        apply bounds_add
        · apply Nat.lt_trans (bounds_mul2 ha_2 ha_4); norm_num
        · apply Nat.lt_trans (bounds_sq ha_3); norm_num

      · -- 8. 2 * a3 * a4
        apply Nat.lt_trans (bounds_mul2 ha_3 ha_4); norm_num

      · -- 9. a4 * a4
        apply Nat.lt_trans (bounds_sq ha_4); norm_num

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
