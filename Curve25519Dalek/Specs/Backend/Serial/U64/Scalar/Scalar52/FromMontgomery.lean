/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce

/-! # Spec Theorem for `Scalar52::from_montgomery`

Specification and proof for `Scalar52::from_montgomery`.

This function converts from Montgomery form.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes an input unpacked scalar m in Montgomery form and returns an unpacked scalar u representing
      the value (m * R⁻¹) mod L, where R = 2^260 is the Montgomery constant and L is the group order.
    • This is the inverse operation of as_montgomery.

natural language specs:

    • The function always succeeds (no panic)
    • scalar_to_nat(u) * R = scalar_to_nat(m) mod L
-/







/-- **Spec for `from_montgomery_loop`**:
- The loop copies limbs from the Scalar52 (5 × U64) into a 9-element U128 array
- When called with i = 0 and input limbs initialized to zeros, the resulting wide representation
  has the same natural number value as the input Scalar52
- Always succeeds (no panic)
-/
@[progress]
theorem from_montgomery_loop_spec (m : Scalar52) :
    ∃ result,
    from_montgomery_loop m (Array.repeat 9#usize 0#u128) 0#usize = ok result ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat m
    := by

    unfold from_montgomery_loop
    unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    rw [if_pos (by decide)]


    unfold from_montgomery_loop
    unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index

    progress as ⟨i1_1, h1_1⟩
    progress as ⟨i2_1, h2_1⟩
    progress as ⟨a_1, ha_1⟩
    progress as ⟨i3_1, hi3_1⟩
    have : i3_1 < 5#usize := by
      rw [show i3_1 = 1#usize by scalar_tac]
      decide
    rw [if_pos this]


    unfold from_montgomery_loop
    unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index

    progress as ⟨i1_2, h1_2⟩
    progress as ⟨i2_2, h2_2⟩
    progress as ⟨a_2, ha_2⟩
    progress as ⟨i3_2, hi3_2⟩
    have : i3_2 < 5#usize := by
      rw [show i3_2 = 2#usize by scalar_tac]
      decide
    rw [if_pos this]

    unfold from_montgomery_loop
    unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index

    progress as ⟨i1_3, h1_3⟩
    progress as ⟨i2_3, h2_3⟩
    progress as ⟨a_3, ha_3⟩
    progress as ⟨i3_3, hi3_3⟩
    have : i3_3 < 5#usize := by
      rw [show i3_3 = 3#usize by scalar_tac]
      decide
    rw [if_pos this]

    unfold from_montgomery_loop
    unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index

    progress as ⟨i1_4, h1_4⟩
    progress as ⟨i2_4, h2_4⟩
    progress as ⟨a_4, ha_4⟩
    progress as ⟨i3_4, hi3_4⟩
    have : i3_4 < 5#usize := by
      rw [show i3_4 = 4#usize by scalar_tac]
      decide
    rw [if_pos this]

    unfold from_montgomery_loop
    unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index

    progress as ⟨i1_5, h1_5⟩
    progress as ⟨i2_5, h2_5⟩
    progress as ⟨a_5, ha_5⟩
    progress as ⟨i3_5, hi3_5⟩
    have : ¬(i3_5 < 5#usize) := by
      rw [show i3_5 = 5#usize by scalar_tac]
      decide
    rw [if_neg this]

    progress*

    unfold Scalar52_as_Nat
    unfold Scalar52_wide_as_Nat

    -- Simplify the index values
    have h_i3_vals : i3_1 = 1#usize ∧ i3_2 = 2#usize ∧ i3_3 = 3#usize ∧ i3_4 = 4#usize := by
      constructor <;> scalar_tac
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h_i3_vals

    -- Split the sum: range 9 = range 5 ∪ [5,9)
    rw [show Finset.range 9 = Finset.range 5 ∪ Finset.Ico 5 9 by
      ext x; simp [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega]
    rw [Finset.sum_union (by decide : Disjoint (Finset.range 5) (Finset.Ico 5 9))]

      -- everything from index 5 to 8 is still zero
    have h_a5_zero :
        ∀ i : ℕ, 5 ≤ i → i < 9 → a_5[i]! = (0#u128) := by
        intro i hi_le hi_lt
        -- a_5 was built by setting only indices 0-4, so indices 5-8 remain 0
        have : i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> (
          rw [ha_5, ha_4, ha_3, ha_2, ha_1]
          simp [Array.repeat]
        )

    -- for the first 5 indices, a_5 entries are equal to m entries
    have h_a5_eq_m :
        ∀ i : ℕ, i < 5 → (a_5[i]! : ℕ) = (m[i]! : ℕ) := by
        intro i hi_lt
        -- a_5 was built by setting indices 0-4 to cast values from m
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl <;> (
          rw [ha_5, ha_4, ha_3, ha_2, ha_1]
          simp [Array.repeat, h2_5, h2_4, h2_3, h2_2, h2_1,
                h1_5, h1_4, h1_3, h1_2, h1_1]
        )

    -- Use h_a5_zero to show the sum from 5 to 9 is zero
    have sum_5_to_9_zero : (∑ x ∈ Finset.Ico 5 9, 2 ^ (52 * x) * (a_5[x]! : ℕ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [Finset.mem_Ico] at hi
      rw [h_a5_zero i hi.1 hi.2]
      simp

    rw [sum_5_to_9_zero, add_zero]

    -- Use h_a5_eq_m to show the sum over range 5 for a_5 equals the sum for m
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range] at hi
    rw [h_a5_eq_m i hi]














/-- **Spec and proof concerning `scalar.Scalar52.from_montgomery`**:
- No panic (always returns successfully)
- The result represents the input scalar divided by the Montgomery constant R = 2^260, modulo L
-/
@[progress]
theorem from_montgomery_spec (m : Scalar52) :
    ∃ u,
    from_montgomery m = ok u ∧
    (Scalar52_as_Nat u * R) % L = Scalar52_as_Nat m % L
    := by
    unfold from_montgomery
    progress*


end curve25519_dalek.backend.serial.u64.scalar.Scalar52
