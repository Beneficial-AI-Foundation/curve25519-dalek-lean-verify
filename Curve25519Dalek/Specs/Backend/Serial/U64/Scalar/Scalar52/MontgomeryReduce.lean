/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
-- import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.LFACTOR
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub

import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic

/-! # Spec Theorem for `Scalar52::montgomery_reduce`

Specification and proof for `Scalar52::montgomery_reduce`.

This function performs Montgomery reduction.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64
open Polynomial
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262

/-
natural language description:

    • **Motivation**: The Montgomery form `M(x) := x * R`, where `R = 2^{260} = 2^{5*52}`,
      is used to optimize chains of modular arithmetic operations (like elliptic curve scalar
      multiplication). The isomorphism induced by `* R` changes the multiplication to:
      `MontMul(x,y) := M(x) * M(y) * R⁻¹`. Therefore, instead of computing standard reduction
      (`x % L`) which requires complex division logic, one needs to compute `x * R⁻¹ (mod L)`.
      Montgomery reduction refers to the algorithm that computes this `x * R⁻¹` using efficient
      bitwise shifts.

    • **Mechanism**: The algorithm avoids division by adding multiples of `L` to the input `x`
      until the result is exactly divisible by `R = 2^{260}` (i.e., the lower 260 bits are all zero).
      Since `R = 2^{260}` and limbs are 52 bits, we perform 5 "zeroing" steps (`part1`)
      followed by 4 "result assembly" steps (`part2`).

    • **Part 1: The Zeroing Strategy**
      We iteratively ensure the lowest remaining limb is 0 by adding a carefully chosen multiple of `L`.
      The helper `part1` calculates a "zeroing factor" `p` using the precomputed `LFACTOR`
      (where `LFACTOR * L ≡ -1 (mod 2⁵²)`).

      - **Limb 0 (First part1)**:
        * **Problem**: `limbs[0]` is non-zero. We cannot shift yet.
        * **Action**: Calculate `p` such that `limbs[0] + p * L ≡ 0 (mod 2⁵²)`.
        * **Result**: The sum's lowest 52 bits become 0.
        * **Shift**: We discard these zero bits (effectively dividing by 2⁵²). The carry flows to the next limb.

      *This repeats 5 times (using updated carries) until the entire lower 260 bits are zero.*

    • **Part 2: Result Reconstruction**
      After 5 reductions, the number is divisible by `R`. The helper `part2` extracts the quotient.
      It takes the high-order accumulated bits, slices off the lower 52 bits as a result limb (`w`),
      and passes the remaining upper bits (`carry`) to the next position. This reassembles
      the final 256-bit result (`r0` through `r4`).

natural language specs:

    • For any 9-limb array `a` of u128 values (representing a 512-bit integer):
      - The function returns a `Scalar52` `m` such that:
        `Scalar52_as_Nat(m) * R ≡ U128x9_as_Nat(a) (mod L)`
-/

-- Bridge lemma: converts the existing LFACTOR_spec (on Nat) to the form needed for Int arithmetic
private lemma LFACTOR_prop :
  (↑constants.LFACTOR.val * ↑constants.L[0]!.val : Int) % (2 ^ 52) = (2 ^ 52) - 1 := by

  have h_nat := constants.LFACTOR_spec
  obtain ⟨h_mod_zero, _, _⟩ := h_nat

  have h_cong : (constants.L[0]!.val : Int) % (2^52) = (_root_.L : Int) % (2^52) := by
    rw [← constants.L_spec]; unfold Scalar52_as_Nat
    rw [Finset.sum_range_succ']; zify at h_mod_zero ⊢; simp only [mul_zero, pow_zero, one_mul]
    rw [Int.add_emod]

    have h_tail_div : (∑ x ∈ Finset.range 4, (2:Int)^(52 * (x + 1)) *
      (constants.L[x.succ]!).val) % 2^52 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      use (∑ x ∈ Finset.range 4, (2:Int)^(52 * x) * (constants.L[x.succ]!).val)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      try ring

    rw [h_tail_div, zero_add, Int.emod_emod]

  rw [mul_comm, Int.mul_emod, h_cong, ← Int.mul_emod]
  rw [← Int.add_sub_cancel (_root_.L * ↑constants.LFACTOR.val : Int) 1, Int.sub_emod]; norm_cast;
  rw [h_mod_zero]; exact rfl

/-- The "Montgomery Step": Proves that adding the reduction factor clears the lower 52 bits. -/
private lemma mont_step (x : Int) (p : Int) (carry_out : Int)
    (hp : p = (x * ↑constants.LFACTOR.val) % (2 ^ 52))
    (hcarry : carry_out = (x + p * ↑constants.L[0]!.val) / (2 ^ 52)) :
    x + p * ↑constants.L[0]!.val = carry_out * (2 ^ 52) := by

  have h_div : x + p * ↑constants.L[0]!.val = carry_out * (2 ^ 52) + (x + p * ↑constants.L[0]!.val) % (2 ^ 52) := by
    rw [hcarry]
    rw [mul_comm ((x + p * ↑constants.L[0]!.val) / 2 ^ 52)]
    rw [Int.mul_ediv_add_emod]

  have h_mod_zero : (x + p * ↑constants.L[0]!.val) % (2 ^ 52) = 0 := by
    rw [hp, Int.add_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, mul_assoc, Int.mul_emod]
    rw [LFACTOR_prop]
    have h_neg : (2  ^ 52 - 1) % 2 ^ 52 = -1 % 2 ^ 52 := by ring;
    rw [← Int.zero_emod (2 ^52)]
    have h_cast : (2 : Int) ^ 52 = ((2 ^ 52 : Nat) : Int) := by norm_cast;
    rw [h_cast]
    apply (ZMod.intCast_eq_intCast_iff' _ _ (2^52)).mp
    simp only [Int.cast_add, ZMod.intCast_mod, Int.cast_mul, Int.cast_sub]
    simp only [Nat.reducePow, Nat.cast_ofNat, Int.cast_ofNat, Aeneas.ReduceZMod.reduceZMod,
      Int.cast_one, zero_sub, mul_neg, mul_one, add_neg_cancel, Int.cast_zero]

  rw [h_div, h_mod_zero, add_zero]



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

set_option maxHeartbeats 8000000 in -- Progress will timout otherwise
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
  unfold backend.serial.u64.scalar.IndexScalar52UsizeU64.index

  -- === ROW 0: Compute n0 ===
  progress as ⟨limbs0, h_limbs0⟩         -- Read a[0]
  progress as ⟨carry0, n0, h_carry0, h_n0, h_n0_bound, h_carry0_bound⟩

  -- === ROW 1: Compute n1 ===
  progress as ⟨limbs1, h_limbs1⟩         -- 1. Read a[1]
  progress as ⟨n1_partial, h_n1_partial⟩ -- 2. Compute partial sum: n0 + limbs1
  progress as ⟨L1, h_L1⟩                 -- 3. Read Constant: L[1]
  progress as ⟨product1, h_product1⟩     -- 4. Compute Product: carry0 * L[1]
  progress as ⟨sum1, h_sum1⟩             -- 5. Total Sum: sum1 = n1_partial + product1
  -- Reduction Step: Compute new reduction factor (carry1) and next row carry (n1)
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

  -- === ROW 5: Compute Result Limb 0 (r0) ===
  -- Formula: S5 = n4 + a[5] + carry1 * L4 + carry3 * L2 + carry4 * L1
  progress as ⟨limbs5, h_limbs5⟩         -- 1. Read a[5]
  progress as ⟨n5_partial, h_n5_partial⟩ -- 2. n4 + limbs5
  progress as ⟨prod5_1, h_prod5_1⟩       -- 3. carry1 * L4
  progress as ⟨n5_accum1, h_n5_accum1⟩   -- 4. Accumulate
  progress as ⟨prod5_2, h_prod5_2⟩       -- 5. carry3 * L2
  progress as ⟨n5_accum2, h_n5_accum2⟩   -- 6. Accumulate
  progress as ⟨prod5_3, h_prod5_3⟩       -- 7. carry4 * L1
  progress as ⟨sum5, h_sum5⟩             -- 8. Final Sum S5
  progress as ⟨n5, r0, h_r0, h_n5, h_n5_bounds, h_r0_bound⟩

  -- === ROW 6: Compute Result Limb 1 (r1) ===
  -- Formula: S6 = n5 + a[6] + carry2 * L4 + carry4 * L2
  progress as ⟨limbs6, h_limbs6⟩         -- 1. Read a[6]
  progress as ⟨n6_partial, h_n6_partial⟩ -- 2. n5 + limbs6
  progress as ⟨prod6_1, h_prod6_1⟩       -- 3. carry2 * L4
  progress as ⟨n6_accum1, h_n6_accum1⟩   -- 4. Accumulate
  progress as ⟨prod6_2, h_prod6_2⟩       -- 5. carry4 * L2
  progress as ⟨sum6, h_sum6⟩             -- 6. Final Sum S6
  progress as ⟨n6, r1, h_r1, h_n6, h_n6_bound, h_r1_bound⟩

  -- === ROW 7: Compute Result Limb 2 (r2) ===
  -- Formula: S7 = n6 + a[7] + carry3 * L4
  progress as ⟨limbs7, h_limbs7⟩         -- 1. Read a[7]
  progress as ⟨n7_partial, h_n7_partial⟩ -- 2. n6 + limbs7
  progress as ⟨prod7_1, h_prod7_1⟩       -- 3. carry3 * L4 (Reuse L4)
  progress as ⟨sum7, h_sum7⟩             -- 4. Final Sum S7
  -- Reduction Part 2 -> Returns (carry_out, result_limb)
  -- The carry is 'n7' and the result 'r2'.
  progress as ⟨n7, r2, h_r2, h_n7, h_n7_bound, h_r2_bound⟩

  -- === ROW 8: Compute Result Limb 3 (r3) and Final Carry (r4) ===
  -- Formula: S8 = n7 + a[8] + carry4 * L4
  progress as ⟨limbs8, h_limbs8⟩         -- 1. Read a[8]
  progress as ⟨n8_partial, h_n8_partial⟩ -- 2. n7 + limbs8
  progress as ⟨prod8_1, h_prod8_1⟩       -- 3. carry4 * L4
  progress as ⟨sum8, h_sum8⟩             -- 4. Final Sum S8
  -- Reduction Part 2 -> Returns (carry_out, result_limb)
  -- The "carry out" here is the 5th limb, r4 (as a u128 first). The "result limb" is r3.
  progress as ⟨r4_u128, r3, h_r3, h_r4_u128, h_r4_u128_bound, h_r3_bound⟩

  -- =========================================================
  -- FINAL STEPS: Cast and Conditional Subtraction
  -- =========================================================

  -- Cast the final limb (r4_u128) to U64
  progress as ⟨r4, h_r4⟩

  -- Call the 'sub' function
  progress as ⟨m, h_sub, h_mod, h_bound⟩
  · -- Case ha: Prove input limbs are < 2^52
    intro i hi
    interval_cases i
    <;> simp only [
      Array.make, Array.getElem!_Nat_eq,
      List.length_cons, List.length_nil,
      List.getElem_cons_zero, List.getElem_cons_succ, getElem!_pos,
      zero_add, Nat.reduceAdd, Nat.reducePow, Nat.reduceLT,
      Nat.ofNat_pos, Nat.lt_add_one, Nat.one_lt_ofNat
    ]
    <;> try scalar_tac
    · -- Bounds on r4 < 2 ^ 52
      have h_r4_tight : ↑r4 < (2 : Nat) ^ 52 := by
        -- use this from Aux.lean : theorem Scalar52_top_limb_lt_of_as_Nat_lt (r : Array U64 5#usize)
        -- (h : Scalar52_as_Nat r < 2 ^ 259) : r[4]!.val < 2 ^ 51 := by sorry
        sorry
      exact h_r4_tight
  · -- Case hb: constants.L are valid
    intro i hi
    interval_cases i <;> assumption
  · -- Case ha': Input < 2 * L
    have h_red_bound : Scalar52_as_Nat
      (Array.make 5#usize [r0, r1, r2, r3, r4]
      field.SubShared0FieldElement51SharedAFieldElement51FieldElement51.sub._proof_4) < 2 * L := by
      sorry
    apply lt_of_lt_of_le h_red_bound
    rw [constants.L_spec, Nat.two_mul]
  · -- Case hb': L ≤ L
    rw [constants.L_spec]
  · -- Post-conditions
    refine ⟨?_,h_bound,?_⟩
    · -- Main Equation: Scalar52_as_Nat m * R % L = Scalar52_wide_as_Nat a % L
      zify
      -- Total Montgomery factor C
      let C : Int := (carry0.val : Int) +
                 (carry1.val : Int) * (2^52 : Int) +
                 (carry2.val : Int) * (2^104 : Int) +
                 (carry3.val : Int) * (2^156 : Int) +
                 (carry4.val : Int) * (2^208 : Int)

      let res := Array.make 5#usize [r0, r1, r2, r3, r4]
        field.SubShared0FieldElement51SharedAFieldElement51FieldElement51.sub._proof_4
      have h_core : ↑(Scalar52_wide_as_Nat a) + C * L =
                    ↑(Scalar52_as_Nat res) * R := by
        simp only [Scalar52_wide_as_Nat, Scalar52_as_Nat, R]
        repeat rw [Finset.sum_range_succ]
        simp only [Finset.sum_range_zero, zero_add, mul_zero, pow_zero, mul_one]
        simp only [res, Array.make, Array.getElem!_Nat_eq]

        zify at h_carry0 h_n0 h_carry1 h_n1 h_carry2 h_n2 h_carry3 h_n3 h_carry4 h_n4
        zify at h_n5 h_r0 h_n6 h_r1 h_n7 h_r2 h_r4_u128 h_r3

        have eq0 := mont_step ↑limbs0 ↑carry0 ↑n0 h_carry0 h_n0
        have eq1 := mont_step ↑sum1 ↑carry1 ↑n1 h_carry1 h_n1
        have eq2 := mont_step ↑sum2 ↑carry2 ↑n2 h_carry2 h_n2
        have eq3 := mont_step ↑sum3 ↑carry3 ↑n3 h_carry3 h_n3
        have eq4 := mont_step ↑sum4 ↑carry4 ↑n4 h_carry4 h_n4

        have eq5 : ↑sum5 = ↑n5 * (2^52 : Int) + ↑r0 := by
          rw [h_n5, h_r0, mul_comm, Int.mul_ediv_add_emod]
        have eq6 : ↑sum6 = ↑n6 * (2^52 : Int) + ↑r1 := by
          rw [h_n6, h_r1, mul_comm, Int.mul_ediv_add_emod]
        have eq7 : ↑sum7 = ↑n7 * (2^52 : Int) + ↑r2 := by
          rw [h_n7, h_r2, mul_comm, Int.mul_ediv_add_emod]
        have eq8 : ↑sum8 = ↑r4_u128 * (2^52 : Int) + ↑r3 := by
          rw [h_r4_u128, h_r3, mul_comm, Int.mul_ediv_add_emod]

        simp only [pow_mul]
        generalize hB : (2 ^ 52) = B
        have hC_B : C = ↑carry0 + ↑carry1 * B + ↑carry2 * B^2 + ↑carry3 * B^3 + ↑carry4 * B^4 := by
          simp only [C]
          rw [←hB]
          have h2 : (2:Int)^104 = (2^52)^2 := by rw [←pow_mul];
          have h3 : (2:Int)^156 = (2^52)^3 := by rw [←pow_mul];
          have h4 : (2:Int)^208 = (2^52)^4 := by rw [←pow_mul];
          rw [h2, h3, h4]; simp only [Nat.cast_pow]; rfl

        have hR_B : ↑(2 ^ 260) = B^5 := by rw [←hB, ←pow_mul]

        have h_L_expand : ↑(Scalar52_as_Nat constants.L) =
          1 * (constants.L[0]!) +
          B * (constants.L[1]!)+
          B^2 * (constants.L[2]!) +
          B^3 * (constants.L[3]!) +
          B^4 * (constants.L[4]!) := by
          unfold Scalar52_as_Nat
          rw [←hB]
          repeat rw [Finset.sum_range_succ]
          rw [Finset.sum_range_zero, zero_add]
          simp only [mul_zero, pow_zero, mul_one, pow_mul]

        rw [hC_B, hR_B, ← constants.L_spec, h_L_expand]
        simp only [
          h_limbs0, h_limbs1, h_limbs2, h_limbs3, h_limbs4, h_limbs5, h_limbs6, h_limbs7, h_limbs8,
          h_L1, h_L2, h_L4,
          h_sum1, h_sum2, h_sum3, h_sum4, h_sum5, h_sum6, h_sum7, h_sum8,
          h_n1_partial, h_n2_partial, h_n3_partial, h_n4_partial, h_n5_partial, h_n6_partial, h_n7_partial, h_n8_partial,
          h_product1, h_prod2_0, h_prod2_1, h_prod3_1, h_prod3_2, h_prod4_0, h_prod4_2, h_prod4_3,
          h_prod5_1, h_prod5_2, h_prod5_3, h_prod6_1, h_prod6_2, h_prod7_1, h_prod8_1,
          h_n2_accum, h_n3_accum, h_n4_accum1, h_n4_accum2, h_n5_accum1, h_n5_accum2, h_n6_accum1,
          h_r4
        ] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 ⊢

        clear h_bounds ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8
        clear hL0 hL1 hL2 hL3 hL4
        clear h_n0_bound h_carry0_bound h_n1_bound h_carry1_bound h_n2_bound h_carry2_bound
        clear h_n3_bound h_carry3_bound h_n4_bound h_carry4_bound
        clear h_n5_bounds h_r0_bound h_n6_bound h_r1_bound h_n7_bound h_r2_bound
        clear h_r3_bound

        simp only [one_mul]

        norm_cast at *
        rw [hB] at *

        rw [← h_r4]
        simp only [List.Vector.length_val, UScalar.ofNat_val_eq, Nat.ofNat_pos, getElem!_pos,
          Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one, Array.getElem!_Nat_eq, List.length_cons,
          List.length_nil, zero_add, Nat.reduceAdd, List.getElem_cons_zero, List.getElem_cons_succ]

        have h_cast_r4 : (r4 : Int) = (r4_u128 : Int) := by
          rw [h_r4]
           -- use h_r4_128_bound
          sorry

        norm_cast at eq8 h_cast_r4
        rw [← h_cast_r4] at eq8
        simp only [← getElem!_pos]

        generalize hBz : (B : ℤ) = Bz
        rw [hBz] at *
        clear hB

        let a_coeffs : List ℕ := [↑(a.val[0]!), ↑(a.val[1]!), ↑(a.val[2]!), ↑(a.val[3]!),
                                  ↑(a.val[4]!), ↑(a.val[5]!), ↑(a.val[6]!), ↑(a.val[7]!), ↑(a.val[8]!)]
        let poly_a : Polynomial ℕ := ∑ i ∈ Finset.range 9, monomial i (a_coeffs.getD i 0)

        let C_coeffs : List ℕ := [↑carry0, ↑carry1, ↑carry2, ↑carry3, ↑carry4]
        let poly_C : Polynomial ℕ := ∑ i ∈ Finset.range 5, monomial i (C_coeffs.getD i 0)

        let L_coeffs : List ℕ := [↑(constants.L.val[0]!), ↑(constants.L.val[1]!),
                                  ↑(constants.L.val[2]!), ↑(constants.L.val[3]!),
                                  ↑(constants.L.val[4]!)]
        let poly_L : Polynomial ℕ := ∑ i ∈ Finset.range 5, monomial i (L_coeffs.getD i 0)

        let poly_lhs := poly_a + poly_C * poly_L
        let res_coeffs : List ℕ := [↑r0, ↑r1, ↑r2, ↑r3, ↑r4]
        let poly_res : Polynomial ℕ := ∑ i ∈ Finset.range 5, monomial i (res_coeffs.getD i 0)
        let poly_rhs := poly_res * monomial 5 1

        suffices h_clean : poly_lhs.eval B = poly_rhs.eval B by
          convert h_clean using 1
          · -- LHS
            simp only [poly_lhs, poly_a, poly_C, poly_L, Polynomial.eval_add, Polynomial.eval_mul,
              Polynomial.eval_finset_sum, Polynomial.eval_monomial]
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
            simp [a_coeffs, C_coeffs, L_coeffs]
            ring_nf
          · -- RHS
            simp only [poly_rhs, poly_res, Polynomial.eval_mul, Polynomial.eval_monomial,
              Polynomial.eval_finset_sum]
            repeat rw [Finset.sum_range_succ]
            simp only [Finset.sum_range_zero, zero_add, pow_zero, pow_one]
            simp only [res_coeffs, List.getD_cons_zero, List.getD_cons_succ]
            ring_nf

        zify at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 ⊢
        simp only [poly_lhs, poly_rhs, poly_a, poly_C, poly_L, poly_res, Polynomial.eval_add,
                  Polynomial.eval_mul, Polynomial.eval_monomial,
                  Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
                  pow_zero, pow_one]
        simp only [a_coeffs, C_coeffs, L_coeffs, res_coeffs]
        simp only [List.getD_cons_zero, List.getD_cons_succ]

        zify at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 ⊢

        have h_align0 : (↑(constants.L[0]!) : ℤ) = ↑(constants.L.val[0]!) := by
          simp only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
            Nat.ofNat_pos, getElem!_pos]
        have h_align1 : (↑(constants.L[1]!) : ℤ) = ↑(constants.L.val[1]!) := by
          simp only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
            Nat.ofNat_pos, getElem!_pos]
        have h_align2 : (↑(constants.L[2]!) : ℤ) = ↑(constants.L.val[2]!) := by
          simp only [Array.getElem!_Nat_eq, Nat.ofNat_pos, getElem!_pos]
        have h_align3 : (↑(constants.L[3]!) : ℤ) = ↑(constants.L.val[3]!) := by
          simp only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq]
        have h_align4 : (↑(constants.L[4]!) : ℤ) = ↑(constants.L.val[4]!) := by
          simp only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
            Nat.ofNat_pos, getElem!_pos]

        simp only [h_align0, h_align1, h_align2, h_align3, h_align4] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8

        have h_L3_zero : ↑(constants.L.val[3]!) = (0 : ℤ) := by
          unfold constants.L
          decide

        simp only [h_L3_zero, mul_zero, zero_mul, add_zero]

        linear_combination eq0 + eq1 * B + eq2 * B^2 + eq3 * B^3 + eq4 * B^4 + eq5 * B^5
                           + eq6 * B^6 + eq7 * B^7 + eq8 * B^8

      have h_equiv_int : (Scalar52_as_Nat m : Int) ≡ (Scalar52_as_Nat res : Int) [ZMOD L] := by
        rw [constants.L_spec] at h_sub; change _ ≡ Scalar52_as_Nat res [MOD L] at h_sub
        rw [← Int.natCast_modEq_iff] at h_sub; push_cast at h_sub
        simp only [Int.add_modulus_modEq_iff] at h_sub; exact h_sub

      rw [Int.ModEq.mul_right R h_equiv_int]
      rw [← h_core]
      rw [Int.add_mul_emod_self_right]

    · -- Post-cond: m < 2 ^ 259
      unfold L at h_mod
      apply lt_of_lt_of_le h_mod
      try decide


end curve25519_dalek.backend.serial.u64.scalar.Scalar52
