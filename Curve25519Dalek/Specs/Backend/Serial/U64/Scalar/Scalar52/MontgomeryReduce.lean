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
  carry.val = (sum.val + p.val * (constants.L[0]!).val) / (2 ^ 52) ∧
  carry.val < 2 ^ 77 ∧
  p.val < 2 ^ 52 := by

  -- Proof of the spec
  rw [montgomery_reduce.part1]
  simp only [constants.LFACTOR, constants.L]

  -- We need to prove the bound here once
  -- Logic: sum < 2^128, p < 2^52, L[0] < 2^52
  -- Numerator < 2^128 + 2^104
  -- Result / 2^52 < 2^76 + 2^52 < 2^77
  try scalar_tac
  sorry

@[progress]
private theorem part2_spec (sum : U128) :
  ∃ carry w,
  montgomery_reduce.part2 sum = ok (carry, w) ∧
  w.val = sum.val % (2 ^ 52) ∧
  carry.val = sum.val / (2 ^ 52) ∧
  carry.val < 2 ^ 76 ∧
  w.val < 2 ^ 52 := by -- 2^128 / 2^52 = 2^76

  rw [montgomery_reduce.part2]
  try scalar_tac

  sorry

set_option maxHeartbeats 2000000 in -- Progress will timout otherwise
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

  -- === ROW 0: Compute n0 ===
  progress as ⟨limbs0, h_limbs0⟩         -- Read a[0]
  progress as ⟨carry0, n0, h_carry0, h_n0, h_n0_bound, h_carry0_bound⟩

  -- === ROW 1: Compute n1 ===
  progress as ⟨limbs1, h_limbs1⟩         -- 1. Read a[1]
  progress as ⟨n1_partial, h_n1_partial⟩ -- 2. Compute partial sum: n0 + limbs1
  progress as ⟨L1, h_L1⟩                 -- 3. Read Constant: L[1]
  progress as ⟨product1, h_product1⟩     -- 4. Compute Product: carry0 * L[1]
  progress as ⟨sum1, h_sum1⟩             -- 5. Total Sum: sum1 = n1_partial + product1
  -- 6. Reduction Step: Compute new reduction factor (carry1) and next row carry (n1)
  progress as ⟨carry1, n1, h_carry1, h_n1, h_n1_bound, h_carry1_bound⟩

  -- === ROW 2: Compute n2 ===
  progress as ⟨limbs2, h_limbs2⟩         -- 1. Read a[2]
  progress as ⟨n2_partial, h_n2_partial⟩ -- 2. n1 + limbs2
  progress as ⟨L2, h_L2⟩                 -- 3. Read L[2]
  progress as ⟨prod2_0, h_prod2_0⟩       -- 4. carry0 * L[2]
  progress as ⟨n2_accum, h_n2_accum⟩     -- 5. Add carry0 term: n2_partial + prod2_0
  progress as ⟨prod2_1, h_prod2_1⟩       -- 6. carry1 * L[1] (Uses L1 from Row 1)
  progress as ⟨sum2, h_sum2⟩             -- 7. Final Sum: n2_accum + prod2_1
  progress as ⟨carry2, n2, h_carry2, h_n2, h_n2_bound, h_carry2_bound⟩

  -- === ROW 3: Compute n3 ===
  progress as ⟨limbs3, h_limbs3⟩         -- 1. Read a[3]
  progress as ⟨n3_partial, h_n3_partial⟩ -- 2. n2 + limbs3
  progress as ⟨prod3_1, h_prod3_1⟩       -- 3. carry1 * L[2] (Reuses L2 from Row 2)
  progress as ⟨n3_accum, h_n3_accum⟩     -- 4. n3_partial + prod3_1
  progress as ⟨prod3_2, h_prod3_2⟩       -- 5. carry2 * L[1] (Reuses L1 from Row 1)
  progress as ⟨sum3, h_sum3⟩             -- 6. Final Sum: n3_accum + prod3_2
  progress as ⟨carry3, n3, h_carry3, h_n3, h_n3_bound, h_carry3_bound⟩

  -- === ROW 4: Compute n4 ===
  progress as ⟨limbs4, h_limbs4⟩         -- 1. Read a[4]
  progress as ⟨n4_partial, h_n4_partial⟩ -- 2. n3 + limbs4
  progress as ⟨L4, h_L4⟩                 -- 3. Read L[4]
  progress as ⟨prod4_0, h_prod4_0⟩       -- 4. carry0 * L[4]
  progress as ⟨n4_accum1, h_n4_accum1⟩   -- 5. Add: n4_partial + prod4_0
  progress as ⟨prod4_2, h_prod4_2⟩       -- 6. carry2 * L[2] (Reuses L2)
  progress as ⟨n4_accum2, h_n4_accum2⟩   -- 7. Add: n4_accum1 + prod4_2
  progress as ⟨prod4_3, h_prod4_3⟩       -- 8. carry3 * L[1] (Reuses L1)
  progress as ⟨sum4, h_sum4⟩             -- 9. Total: n4_accum2 + prod4_3
  progress as ⟨carry4, n4, h_carry4, h_n4, h_n4_bound, h_carry4_bound⟩

  -- =========================================================
  -- CLEANUP STEP
  -- Clear intermediate accumulators from Rows 0-4
  -- Keep: a, limbs*, carry*, n*, L*, and their bounds
  -- =========================================================
  try clear n1_partial product1 sum1
  try clear h_n1_partial h_product1 h_sum1
  try clear n2_partial prod2_0 n2_accum prod2_1 sum2
  try clear h_n2_partial h_n2_accum h_prod2_1 h_sum2
  try clear n3_partial prod3_1 n3_accum prod3_2 sum3
  try clear h_n3_partial h_prod3_1 h_n3_accum h_prod3_2 h_sum3
  try clear n4_partial prod4_0 n4_accum1 prod4_2 n4_accum2 prod4_3 sum4
  try clear h_n4_partial h_prod4_0 h_n4_accum1 h_prod4_2 h_n4_accum2 h_prod4_3 h_sum4

  -- === ROW 5: Compute Result Limb 0 (r0) ===
  -- Formula: S5 = n4 + a[5] + carry1*L4 + carry3*L2 + carry4*L1
  progress as ⟨limbs5, h_limbs5⟩         -- 1. Read a[5]
  progress as ⟨n5_partial, h_n5_partial⟩ -- 2. n4 + limbs5
  progress as ⟨prod5_1, h_prod5_1⟩       -- 3. carry1 * L4
  progress as ⟨n5_accum1, h_n5_accum1⟩   -- 4. Accumulate
  progress as ⟨prod5_2, h_prod5_2⟩       -- 5. carry3 * L2
  progress as ⟨n5_accum2, h_n5_accum2⟩   -- 6. Accumulate
  progress as ⟨prod5_3, h_prod5_3⟩       -- 7. carry4 * L1
  progress as ⟨sum5, h_sum5⟩             -- 8. Final Sum S5
  -- 9. Reduction Part 2: Returns (carry_out, result_limb)
  progress as ⟨n5, r0, h_n5, h_r0, h_n5_bounds, h_r0_bound⟩

  try clear n5_partial prod5_1 n5_accum1 prod5_2 n5_accum2 prod5_3 sum5
  try clear h_n5_partial h_prod5_1 h_n5_accum1 h_prod5_2 h_n5_accum2 h_prod5_3 h_sum5

  -- === ROW 6: Compute Result Limb 1 (r1) ===
  -- Formula: S6 = n5 + a[6] + carry2*L4 + carry4*L2
  progress as ⟨limbs6, h_limbs6⟩         -- 1. Read a[6]
  progress as ⟨n6_partial, h_n6_partial⟩ -- 2. n5 + limbs6
  progress as ⟨prod6_1, h_prod6_1⟩       -- 3. carry2 * L4
  progress as ⟨n6_accum1, h_n6_accum1⟩   -- 4. Accumulate
  progress as ⟨prod6_2, h_prod6_2⟩       -- 5. carry4 * L2
  progress as ⟨sum6, h_sum6⟩             -- 6. Final Sum S6
  progress as ⟨n6, r1, h_n6, h_r1, h_n6_bound, h_r1_bound⟩

  try clear n6_partial prod6_1 n6_accum1 prod6_2 sum6
  try clear h_n6_partial h_prod6_1 h_n6_accum1 h_prod6_2 h_sum6

  
  sorry

  -- -- === ROW 5: Compute r0 (Division starts) ===
  -- -- Operations: + m(n1, L[4]) + m(n3, L[2]) + m(n4, L[1])
  -- set_option maxHeartbeats 4000000 in
  -- (
  --  progress -- m(n1, L[4])
  --  progress -- +
  --  progress -- m(n3, L[2])
  --  progress -- +
  --  progress -- m(n4, L[1])
  --  progress -- +
  --  progress as ⟨carry5, r0⟩ -- part2 call
  -- )

  -- -- === ROW 6: Compute r1 ===
  -- -- Operations: + m(n2, L[4]) + m(n4, L[2])
  -- set_option maxHeartbeats 4000000 in
  -- (
  --  progress -- m(n2, L[4])
  --  progress -- +
  --  progress -- m(n4, L[2])
  --  progress -- +
  --  progress as ⟨carry6, r1⟩ -- part2 call
  -- )








  -- -- === ROW 7: Compute r2 ===
  -- -- Operations: + m(n3, L[4])
  -- progress -- m(n3, L[4])
  -- progress -- +
  -- progress as ⟨carry7, r2⟩ -- part2 call

  -- -- === ROW 8: Compute r3 ===
  -- -- Operations: + m(n4, L[4])
  -- progress -- m(n4, L[4])
  -- progress -- +
  -- progress as ⟨carry8, r3⟩ -- part2 call

  -- -- === Final Subtraction ===
  -- progress -- cast carry to r4
  -- progress as ⟨m_final⟩ -- Scalar52::sub

  -- -- === Post-Conditions ===
  -- split_ands
  -- · sorry -- 1. Returns ok
  -- · sorry -- 2. Modular arithmetic correctness
  -- · sorry -- 3. Limb bounds (Scalar52::sub output spec)
  -- · sorry -- 4. Total bound (Scalar52_as_Nat m < 2^259)





/- OLD ATTEMPT

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

  progress as ⟨i0, hi₀⟩; progress as ⟨b1, i1, h_b₁, h_i₁, h_i1_bound⟩;

  generalize h_b1_val : ((↑a)[0]!).val * constants.LFACTOR.val % 2 ^ 52 = b1_val
  generalize h_i1_val : ( ((↑a)[0]!).val + b1_val * ((constants.L)[0]!).val ) / 2 ^ 52 = i1_val
  have h_b1_bound : b1_val < 2^52 := by
      rw [← h_b1_val]; apply Nat.mod_lt; norm_num
  have h_i1_bound : i1_val < 2^76 := by
    rw [← h_i1_val]; apply Nat.div_lt_of_lt_mul; try scalar_tac -- Solves (a[0] + b1*L[0]) < 2^128

  progress as ⟨i2, h_i₂⟩; progress as ⟨i3, h_i₃⟩; progress as ⟨i4, h_i₄⟩; progress as ⟨i5, h_i₅⟩;

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

  progress as ⟨i7, i8 , h_i₇, h_i₈⟩;

  -- generalize h_i7 : _ * constants.LFACTOR.val % 2 ^ 52 = i7_val
  -- have h_i7_bound : i7_val < 2^52 := by
  --     rw [← h_i7]; apply Nat.mod_lt; norm_num

  progress as ⟨i9, h_i₉⟩; progress as ⟨i10, h_i₁₀⟩;
  progress as ⟨i11, h_i₁₁⟩; progress as ⟨i12, h_i₁₂⟩;

  progress as ⟨i13, h_i₁₃⟩
  · --

    sorry
  · --
    sorry

-/


  -- <;> try (
  --   simp only [h_i₁₂, h_i₁₀, h_i₈, h_i₉, h_i₁₁, h_i₇, h_i₆, h_i₅, h_i₃, h_i₁, hi₀, h_b₁, h_i₂, h_i₄]
  --   simp only [Array.getElem!_Nat_eq] at *

  --   generalize h_carry : ( _ / 2^52 ) = carry

  --   have h_mod_bound : i6.val * constants.LFACTOR.val % 2 ^ 52 < 2 ^ 52 := by
  --     apply Nat.mod_lt
  --     norm_num

  --   have h_carry_bound : carry < 2^76 := by
  --     rw [← h_carry]
  --     apply Nat.div_lt_of_lt_mul
  --     try scalar_tac

  --   try scalar_tac
  --   )

  -- progress as ⟨i14, h_i₁₄⟩; progress as ⟨i15, h_i₁₅⟩;
  -- · -- Solve subgoal for i13 + i14
  --   simp only [h_i₁₃, h_i₁₄, h_i₁₀, h_i₁₂, h_i₉, h_i₈, h_i₇,h_i₆, h_i₅, h_i₃, h_b₁, h_i₁₁, h_i₄,
  --               h_i₂, h_i₁, hi₀]
  --   simp only [Array.getElem!_Nat_eq] at *

  --   generalize h_i8_val : _ / 2^52 = i8_val

  --   -- Bound i8 (< 2^76)
  --   have h_i8_bound : i8_val < 2^76 := by
  --     rw [← h_i8_val]
  --     apply Nat.div_lt_of_lt_mul
  --     try scalar_tac

  --   try scalar_tac
  --   sorry
  -- · --
  --   sorry




  -- progress as ⟨i16, i17, h_i₁₆, h_i₁₇⟩
  -- progress as ⟨i18, h_i₁₈⟩; progress as ⟨i19, h_i₁₉⟩; progress as ⟨i20, h_i₂₀⟩;
  -- progress as ⟨i21, h_i₂₁⟩; progress as ⟨i22, h_i₂₂⟩; progress as ⟨i23, h_i₂₃⟩;
  -- progress as ⟨i24, i25, h_i₂₄, h_i₂₅⟩; progress as ⟨i26, h_i₂₆⟩; progress as ⟨i27, h_i₂₇⟩
  -- progress as ⟨i28, h_i₂₈⟩; progress as ⟨i29, h_i₂₉⟩;

  -- progress as ⟨i30, h_i₃₀⟩ <;> try (subst h_i₁₈ h_i₂₆ h_i₂₈; try scalar_tac)
  -- -- progress as ⟨i31, h_i₃₁⟩; -- progress as ⟨i32, h_i₃₂⟩

  -- progress as ⟨i31, h_i₃₁⟩


end curve25519_dalek.backend.serial.u64.scalar.Scalar52
