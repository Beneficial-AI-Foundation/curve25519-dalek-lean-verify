/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.LFACTOR

/-! # Spec Theorem for `Scalar52::montgomery_reduce`

Specification and proof for `Scalar52::montgomery_reduce`.

This function performs Montgomery reduction.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262

/-
natural language description:

    • Takes as input a 9-limb array of u128 values (representing a product in polynomial form)
      and performs Montgomery reduction to produce an UnpackedScalar in Montgomery form.

    • Montgomery reduction is the core operation that reduces a product (m * m') back to
      Montgomery form by computing (product * R⁻¹) mod L, where R = 2^260.

    • This is used after polynomial multiplication (mul_internal or square_internal) to
      complete Montgomery multiplication or squaring operations.

natural language specs:

    • For any 9-limb array a of u128 values:
      - The function returns a Scalar52 m such that:
        Scalar52_as_Nat(m) * R ≡ U128x9_as_Nat(a) (mod L)
-/

@[progress]
private theorem part1_spec (sum : U128) :
  ∃ p carry,
  montgomery_reduce.part1 sum = ok (carry, p) ∧
  p.val = (sum.val * constants.LFACTOR) % (2 ^ 52) ∧
  carry.val = (sum.val + p.val * (constants.L[0]!).val) / (2 ^ 52) := by
  unfold montgomery_reduce.part1
  progress*

  sorry

@[progress]
private theorem part2_spec (sum : U128) :
  ∃ carry w,
  montgomery_reduce.part2 sum = ok (carry, w) ∧
  -- w = sum % 2^52
  w.val = sum.val % (2 ^ 52) ∧
  -- carry = sum / 2^52
  carry.val = sum.val / (2 ^ 52) := by
  unfold montgomery_reduce.part2
  progress*

  sorry

set_option maxHeartbeats 1600000 in -- Progress will timout otherwise
/-- **Spec and proof concerning `scalar.Scalar52.montgomery_reduce`**:
- No panic (always returns successfully)
- The result m satisfies the Montgomery reduction property:
  m * R ≡ a (mod L), where R = 2^260 is the Montgomery constant
-/
@[progress]
theorem montgomery_reduce_spec (a : Array U128 9#usize)
    (h_bounds : ∀ i < 9, a[i]!.val < 2 ^ 127) :
    ∃ m,
    montgomery_reduce a = ok m ∧
    (Scalar52_as_Nat m * R) % L = Scalar52_wide_as_Nat a % L ∧
    (∀ i < 5, m[i]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat m < 2 ^ 259)
    := by
  -- 1. Instantiate ALL array bounds explicitly.
  have ha0 : a[0]!.val < 2^127 := h_bounds 0 (by decide)
  have ha1 : a[1]!.val < 2^127 := h_bounds 1 (by decide)
  have ha2 : a[2]!.val < 2^127 := h_bounds 2 (by decide)
  have ha3 : a[3]!.val < 2^127 := h_bounds 3 (by decide)
  have ha4 : a[4]!.val < 2^127 := h_bounds 4 (by decide)
  have ha5 : a[5]!.val < 2^127 := h_bounds 5 (by decide)
  have ha6 : a[6]!.val < 2^127 := h_bounds 6 (by decide)
  have ha7 : a[7]!.val < 2^127 := h_bounds 7 (by decide)
  have ha8 : a[8]!.val < 2^127 := h_bounds 8 (by decide)

  -- 2. Instantiate L bounds
  have hL0 : (constants.L[0]!).val < 2 ^ 52 := constants.L_limbs_spec 0#usize (by decide)
  have hL1 : (constants.L[1]!).val < 2 ^ 52 := constants.L_limbs_spec 1#usize (by decide)
  have hL2 : (constants.L[2]!).val < 2 ^ 52 := constants.L_limbs_spec 2#usize (by decide)
  have hL3 : (constants.L[3]!).val < 2 ^ 52 := constants.L_limbs_spec 3#usize (by decide)
  have hL4 : (constants.L[4]!).val < 2 ^ 52 := constants.L_limbs_spec 4#usize (by decide)

  unfold montgomery_reduce
  unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index

  progress as ⟨i0, hi₀⟩; progress as ⟨b1, i1, h_b₁, h_i₁⟩; progress as ⟨i2, h_i₂⟩
  progress as ⟨i3, h_i₃⟩; progress as ⟨i4, h_i₄⟩; progress as ⟨i5, h_i₅⟩;


  progress as ⟨i6, h_i₆⟩
  <;> try (
    simp only [h_i₅, h_i₃, h_b₁, hi₀, h_i₁]
    simp only [Array.getElem!_Nat_eq] at *

    generalize h_carry : ( _ / 2^52 ) = carry

    have h_mod_bound : ((↑a)[0]!).val * constants.LFACTOR.val % 2 ^ 52 < 2 ^ 52 := by
        apply Nat.mod_lt
        norm_num

    have h_carry_bound : carry < 2^76 := by
      rw [← h_carry]
      apply Nat.div_lt_of_lt_mul
      try scalar_tac

    try scalar_tac
    )

  progress as ⟨i7, i8 , h_i₇, h_i₈⟩; progress as ⟨i9, h_i₉⟩; progress as ⟨i10, h_i₁₀⟩;
  progress as ⟨i11, h_i₁₁⟩; progress as ⟨i12, h_i₁₂⟩;

  progress as ⟨i13, h_i₁₃⟩
  <;> try (
    simp only [h_i₁₂, h_i₁₀, h_i₈, h_i₉, h_i₁₁, h_i₇, h_i₆, h_i₅, h_i₃, h_i₁, hi₀, h_b₁, h_i₂, h_i₄]
    simp only [Array.getElem!_Nat_eq] at *
    generalize h_b1 : ((a[0]!).val * constants.LFACTOR.val % 2 ^ 52) = b1_val

    generalize h_i7 : _ * constants.LFACTOR.val % 2 ^ 52 = i7_val

    have h_b1_bound : b1_val < 2^52 := by
      rw [← h_b1]
      apply Nat.mod_lt; norm_num

    generalize h_carry : ( _ / 2^52 ) = carry

    have h_b1_bound : b1_val < 2^52 := by
      rw [← h_b1]; apply Nat.mod_lt; norm_num

    have h_i7_bound : i7_val < 2^52 := by
      rw [← h_i7]; apply Nat.mod_lt; norm_num

    have h_mod_bound : i6.val * constants.LFACTOR.val % 2 ^ 52 < 2 ^ 52 := by
      apply Nat.mod_lt
      norm_num

    have h_carry_bound : carry < 2^76 := by
      rw [← h_carry]
      apply Nat.div_lt_of_lt_mul
      try scalar_tac

    try scalar_tac
    )

  progress as ⟨i14, h_i₁₄⟩; progress as ⟨i15, h_i₁₅⟩;
  · -- Solve subgoal for i13 + i14
    simp only [h_i₁₃, h_i₁₄, h_i₁₀, h_i₁₂, h_i₉, h_i₈, h_i₇,h_i₆, h_i₅, h_i₃, h_b₁, h_i₁₁, h_i₄,
                h_i₂, h_i₁, hi₀]
    simp only [Array.getElem!_Nat_eq] at *

    generalize h_b1_val : ((↑a)[0]!).val * constants.LFACTOR.val % 2 ^ 52 = b1_val
    generalize h_i1_val : ( (↑a)[0]!).val + b1_val * ((constants.L)[0]!).val  / 2 ^ 52 = i1_val
    generalize h_i7_val : _ * constants.LFACTOR.val % 2 ^ 52 = i7_val
    generalize h_i8_val : _ / 2^52 = i8_val

    have h_b1_bound : b1_val < 2^52 := by
      rw [← h_b1_val]
      apply Nat.mod_lt; norm_num

    have h_i1_bound : i1_val < 2^76 := by
      rw [← h_i1_val]
      --apply Nat.div_lt_of_lt_mul
      try scalar_tac -- Solves (a[0] + b1*L[0]) < 2^128
      sorry

    -- Bound i7 (< 2^52)
    have h_i7_bound : i7_val < 2^52 := by
      rw [← h_i7_val]
      apply Nat.mod_lt; norm_num

    -- Bound i8 (< 2^76)
    have h_i8_bound : i8_val < 2^76 := by
      rw [← h_i8_val]
      apply Nat.div_lt_of_lt_mul
      try scalar_tac

    try scalar_tac
    sorry
  · --

    sorry


  -- progress as ⟨i16, i17, h_i₁₆, h_i₁₇⟩
  -- progress as ⟨i18, h_i₁₈⟩; progress as ⟨i19, h_i₁₉⟩; progress as ⟨i20, h_i₂₀⟩;
  -- progress as ⟨i21, h_i₂₁⟩; progress as ⟨i22, h_i₂₂⟩; progress as ⟨i23, h_i₂₃⟩;
  -- progress as ⟨i24, i25, h_i₂₄, h_i₂₅⟩; progress as ⟨i26, h_i₂₆⟩; progress as ⟨i27, h_i₂₇⟩
  -- progress as ⟨i28, h_i₂₈⟩; progress as ⟨i29, h_i₂₉⟩;

  -- progress as ⟨i30, h_i₃₀⟩ <;> try (subst h_i₁₈ h_i₂₆ h_i₂₈; try scalar_tac)
  -- -- progress as ⟨i31, h_i₃₁⟩; -- progress as ⟨i32, h_i₃₂⟩

  -- progress as ⟨i31, h_i₃₁⟩


end curve25519_dalek.backend.serial.u64.scalar.Scalar52
