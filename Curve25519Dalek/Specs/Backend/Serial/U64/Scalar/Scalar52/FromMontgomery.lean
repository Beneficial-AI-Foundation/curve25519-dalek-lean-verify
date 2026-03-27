/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce

/-! # Spec Theorem for `Scalar52::from_montgomery`

This function converts from Montgomery form.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
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

/-- Strange that this result is required, how can the argument be made smoother where this is used?. -/
theorem set_getElem!_eq (l : List U128) (a : U128) (i : ℕ) (h : i < l.length) :
    (l.set i (a))[i]! = a := by
  simp_all only [List.getElem!_set]

/-- Strange that this result is required, how can the argument be made smoother? -/
theorem zero_array (i : ℕ) (hi : i < 9) :
    ((Array.repeat 9#usize 0#u128) : List U128)[i]!.val = 0 := by
  interval_cases i <;> exact rfl

/-- **Spec theorem for `from_montgomery_loop`**:
- Specification for the loop that copies limbs from a Scalar52 (5 × U64) into a 9-element U128 array
- Ensures that:
  - Limbs at indices [i, 5) are copied from the input Scalar52 to the result array
  - Limbs at indices [5, 9) remain unchanged from the input limbs array
  - Limbs at indices [0, i) remain unchanged from the input limbs array -/
@[step]
theorem from_montgomery_loop_spec (self : Scalar52) (limbs : Array U128 9#usize) (i : Usize)
    (hi : i.val ≤ 5) :
    from_montgomery_loop self limbs i ⦃ (result : Std.Array U128 9#usize) =>
      (∀ j < 5, i.val ≤ j → result[j]! = UScalar.cast .U128 self[j]!) ∧
      (∀ j < 9, 5 ≤ j → result[j]! = limbs[j]!) ∧
      (∀ j < i.val, result[j]! = limbs[j]!) ⦄ := by
  unfold from_montgomery_loop
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  split
  · step*
    refine ⟨fun j hj hij ↦ ?_, fun j hj hj' ↦ ?_, ?_⟩
    · by_cases hc : i = j
      · rw [result_post3 j (by simp_all), a_post, i2_post, i1_post, ← hc]
        simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
        apply set_getElem!_eq
        simp only [List.Vector.length_val, UScalar.ofNatCore_val_eq]; agrind
      · exact result_post1 j hj (by omega)
    · rw [result_post2 j hj hj']
      have : i ≠ j := by agrind
      simp [*]
    · intro j _
      have := result_post3 j (by omega)
      simp_all
  · step*
termination_by 5 - i.val
decreasing_by scalar_decr_tac

/-- **Spec theroem for `scalar.Scalar52.from_montgomery`**:
- The result represents the input scalar divided by the Montgomery constant R = 2^260, modulo L -/
@[step]
theorem from_montgomery_spec (self : Scalar52) (h_bounds : ∀ i < 5, self[i]!.val < 2 ^ 62) :
    from_montgomery self ⦃ (result : Scalar52) =>
      (Scalar52_as_Nat result * R) % L = Scalar52_as_Nat self % L ∧
      Scalar52_as_Nat result < L ∧ ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by
  unfold from_montgomery
  step*
  · intro i hi
    by_cases h_lt : i < 5
    · rw [limbs1_post1 i h_lt (Nat.zero_le i)]; specialize h_bounds i h_lt; simp only [Array.getElem!_Nat_eq,
      UScalarTy.U64_numBits_eq, UScalarTy.U128_numBits_eq, Nat.reduceLeDiff,
      UScalar.cast_val_mod_pow_greater_numBits_eq, Nat.reducePow];
      agrind
    · have h_ge : 5 ≤ i := by agrind
      rw [limbs1_post2 i hi h_ge]
      simp only [Array.repeat] at ⊢
      simp only [getElem!, List.getElem?_replicate]
      simp_all only [Array.getElem!_Nat_eq, Nat.reducePow, zero_le, forall_const, not_lt_zero',
        IsEmpty.forall_iff, not_lt, UScalar.ofNatCore_val_eq, reduceIte, Nat.ofNat_pos]
  · refine ⟨?_, by assumption, by assumption⟩
    rw [result_post1]
    simp only [Scalar52_as_Nat, Scalar52_wide_as_Nat, Finset.sum_range_succ]
    simp [-Nat.reducePow, *]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
