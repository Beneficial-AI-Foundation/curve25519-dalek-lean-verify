/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
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

set_option linter.hashCommand false
#setup_aeneas_simps

/-- Strange that this result is required, how can the argument be made smoother where this is used?. -/
theorem set_getElem!_eq (l : List U128) (a : U128) (i : ℕ) (h : i < l.length) :
    (l.set i (a))[i]! = a := by
  simp_all only [List.getElem!_set]

/-- Strange that this result is required, how can the argument be made smoother where this is used?. -/
theorem zero_array (i : ℕ) (hi : i < 9) :
    ((Array.repeat 9#usize 0#u128) : List U128)[i]!.val = 0 := by
  interval_cases i <;> exact rfl

@[progress]
theorem from_montgomery_loop_spec (self : Scalar52) (limbs : Array U128 9#usize) (i : Usize)
    (hi : i.val ≤ 5) :
    ∃ result, from_montgomery_loop self limbs i = ok result ∧
    (∀ j < 5, i.val ≤ j → result[j]! = UScalar.cast .U128 self[j]!) ∧
    (∀ j < 9, 5 ≤ j → result[j]! = limbs[j]!) ∧
    (∀ j < i.val, result[j]! = limbs[j]!) := by
  unfold from_montgomery_loop
  unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  split
  · progress*
    refine ⟨fun j hj hij ↦ ?_, fun j hj hj' ↦ ?_, ?_⟩
    · by_cases hc : i = j
      · rw [res_post_3 j (by simp_all), a_post, i2_post, i1_post, ← hc]
        simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
        apply set_getElem!_eq
        simp; grind
      · exact res_post_1 j hj (by omega)
    · rw [res_post_2 j hj hj']
      have : i ≠ j := by scalar_tac
      simp [*]
    · intro j _
      have := res_post_3 j (by omega)
      simp_all
  · progress*
    have : i.val = 5 := by scalar_tac
    grind
termination_by 5 - i.val
decreasing_by scalar_decr_tac


-- /-- **Spec for `from_montgomery_loop`**:
-- - The loop simply copies limbs from the Scalar52 (5 × U64) into a 9-element U128 array
-- - When called with i = 0 and input limbs initialized to zeros, the resulting wide representation
--   has the same natural number value as the input Scalar52
-- - Always succeeds (no panic)
-- -/
-- @[progress]
-- theorem from_montgomery_loop_spec' (m : Scalar52) :
--     ∃ result,
--     from_montgomery_loop m (Array.repeat 9#usize 0#u128) 0#usize = ok result ∧
--     Scalar52_wide_as_Nat result = Scalar52_as_Nat m
--     := by

--     unfold from_montgomery_loop Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
--     rw [if_pos (by decide)]

--     -- Loop iterations 1-4
--     (unfold from_montgomery_loop Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
--      progress as ⟨i1_1, h1_1⟩; progress as ⟨i2_1, h2_1⟩; progress as ⟨a_1, ha_1⟩; progress as ⟨i3_1, _⟩
--      rw [if_pos (by scalar_tac)])
--     (unfold from_montgomery_loop Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
--      progress as ⟨i1_2, h1_2⟩; progress as ⟨i2_2, h2_2⟩; progress as ⟨a_2, ha_2⟩; progress as ⟨i3_2, _⟩
--      rw [if_pos (by scalar_tac)])
--     (unfold from_montgomery_loop Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
--      progress as ⟨i1_3, h1_3⟩; progress as ⟨i2_3, h2_3⟩; progress as ⟨a_3, ha_3⟩; progress as ⟨i3_3, _⟩
--      rw [if_pos (by scalar_tac)])
--     (unfold from_montgomery_loop Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
--      progress as ⟨i1_4, h1_4⟩; progress as ⟨i2_4, h2_4⟩; progress as ⟨a_4, ha_4⟩; progress as ⟨i3_4, _⟩
--      rw [if_pos (by scalar_tac)])

--     -- Loop iteration 5 (exit)
--     unfold from_montgomery_loop Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
--     progress as ⟨i1_5, h1_5⟩; progress as ⟨i2_5, h2_5⟩; progress as ⟨a_5, ha_5⟩; progress as ⟨i3_5, _⟩
--     rw [if_neg (by scalar_tac)]
--     progress*

--     -- Show that Scalar52_wide_as_Nat a_5 = Scalar52_as_Nat m, whereby a_5 has been built during the loop
--     unfold Scalar52_as_Nat Scalar52_wide_as_Nat
--     obtain ⟨rfl, rfl, rfl, rfl⟩ : i3_1 = 1#usize ∧ i3_2 = 2#usize ∧ i3_3 = 3#usize ∧ i3_4 = 4#usize := by
--       constructor <;> scalar_tac
--     rw [show Finset.range 9 = Finset.range 5 ∪ Finset.Ico 5 9 by ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega]
--     rw [Finset.sum_union (by decide)]

--     have h_zero : ∀ i, 5 ≤ i → i < 9 → a_5[i]! = 0#u128 := by
--       intro i _ _; interval_cases i <;>
--       simp only [ha_5, ha_4, ha_3, ha_2, ha_1, Array.repeat, UScalar.ofNat_val_eq, List.reduceReplicate,
--         Array.getElem!_Nat_eq, Array.set_val_eq, List.set_cons_zero, List.set_cons_succ, List.length_cons, List.length_nil,
--         zero_add, Nat.reduceAdd, Nat.reduceLT, getElem!_pos, List.getElem_cons_succ, List.getElem_cons_zero]

--     have : ∑ x ∈ Finset.Ico 5 9, 2 ^ (52 * x) * (a_5[x]! : ℕ) = 0 := by
--       refine Finset.sum_eq_zero fun i hi => ?_; simp only [Finset.mem_Ico] at hi
--       rw [h_zero i hi.1 hi.2]; simp only [UScalar.ofNat_val_eq, mul_zero]

--     rw [this, add_zero]; refine Finset.sum_congr rfl fun i hi => ?_; simp only [Finset.mem_range] at hi
--     interval_cases i <;>
--     simp [ha_5, ha_4, ha_3, ha_2, ha_1, Array.repeat, h2_5, h2_4, h2_3, h2_2, h2_1, h1_5, h1_4, h1_3, h1_2, h1_1]


/-- **Spec and proof concerning `scalar.Scalar52.from_montgomery`**:
- No panic (always returns successfully)
- The result represents the input scalar divided by the Montgomery constant R = 2^260, modulo L
-/
@[progress]
theorem from_montgomery_spec (m : Scalar52) :
    ∃ u, from_montgomery m = ok u ∧
    (Scalar52_as_Nat u * R) % L = Scalar52_as_Nat m % L := by
  unfold from_montgomery
  progress*
  rw [res_post]
  simp only [Scalar52_as_Nat, Scalar52_wide_as_Nat, Finset.sum_range_succ]
  simp [-Nat.reducePow, *, zero_array]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
