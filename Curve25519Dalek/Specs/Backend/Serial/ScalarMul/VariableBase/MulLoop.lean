/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsProjective
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectivePoint.Double
import Curve25519Dalek.Specs.Window.LookupTable.From
import Curve25519Dalek.Specs.Window.LookupTable.Select
import Curve25519Dalek.ExternallyVerified
import Mathlib

/-! # Spec Theorem for `variable_base::mul_loop`

Specification for the Horner radix-16 signed-digit main loop of variable-base scalar
multiplication. Iterates `i = 63, 62, ..., 1` counting down; at each step performs 4
doublings on `tmp1` then adds `select(lookup_table, scalar_digits[i-1])` to accumulate
one more radix-16 digit.

**Source**: curve25519-dalek/src/backend/serial/scalar_mul/variable_base.rs, lines 36-49
(loop 0 of `variable_base::mul`).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.edwards

namespace curve25519_dalek.backend.serial.scalar_mul.variable_base

/-- Partial radix-16 sum from index `i` upwards:
`digits[i] + 16 * digits[i+1] + 16^2 * digits[i+2] + ... + 16^(63-i) * digits[63]`.
Matches Verus's `reconstruct_radix_2w(digits[i..64], 4)`. -/
def I8x64_partial_radix16 (digits : Array Std.I8 64#usize) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (64 - i), (16 : ℤ)^j * (digits[i + j]!).val

/-- At `i = 0`, the partial sum covers all 64 digits (i.e., the full radix-16 encoding). -/
lemma I8x64_partial_radix16_zero (digits : Array Std.I8 64#usize) :
    I8x64_partial_radix16 digits 0 =
      ∑ j ∈ Finset.range 64, (16 : ℤ)^j * (digits[j]!).val := by
  unfold I8x64_partial_radix16
  simp

/-- Horner recurrence for `I8x64_partial_radix16`: extending the sum by one more
digit on the low side multiplies the tail by 16 and adds the new digit. -/
lemma I8x64_partial_radix16_recurrence
    (digits : Array Std.I8 64#usize) (i : ℕ) (hi_pos : 1 ≤ i) (hi_le : i ≤ 64) :
    I8x64_partial_radix16 digits (i - 1) =
      (digits[i - 1]!).val + 16 * I8x64_partial_radix16 digits i := by
  unfold I8x64_partial_radix16
  rw [show 64 - (i - 1) = (64 - i) + 1 from by omega]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.add_zero]
  rw [add_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros j _
  rw [pow_succ]
  have h_idx : i - 1 + (j + 1) = i + j := by omega
  rw [h_idx]
  ring

/-
natural language description:

• Tail-recursive loop for variable-base scalar multiplication. Given counter `i`, table,
  signed digits, and current accumulator `tmp1` representing `partial_i • P`, the loop:
    - If `i = 0`: returns `tmp1`.
    - Else: doubles `tmp1` four times (× 16), converts to extended, selects the
      `(i-1)`-th digit's contribution via `LookupTable.select`, adds it to `tmp1`, and
      recurses on `i - 1`.

• Loop invariant:
    tmp1.toPoint = (I8x64_partial_radix16 scalar_digits i) • P.toPoint.

natural language specs:

• The function always succeeds (no panic).
• The result is a valid CompletedPoint.
• The result represents the full radix-16 sum: `tmp.toPoint = (I8x64_as_Radix16 digits) • P`.
-/

/-- **Spec and proof concerning `variable_base.mul_loop`**:
- No panic (always returns successfully)
- Returns a `CompletedPoint` whose Edwards point equals the full radix-16 reconstruction
  of `scalar_digits`, scaled by `P.toPoint`.
-/
@[step]
theorem mul_loop_spec
    (P : EdwardsPoint) (hP : P.IsValid)
    (lookup_table : window.LookupTable ProjectiveNielsPoint)
    (h_table_valid : ∀ (k : Fin 8), lookup_table.val[k].IsValid)
    (h_table_point : ∀ (k : Fin 8),
        lookup_table.val[k].toPoint = ((k.val + 1 : ℕ) : ℤ) • P.toPoint)
    (scalar_digits : Array Std.I8 64#usize)
    (h_digits_bds : ∀ k < 63,
        -8 ≤ (scalar_digits[k]!).val ∧ (scalar_digits[k]!).val < 8)
    (h_digit_63 : -8 ≤ (scalar_digits[63]!).val ∧ (scalar_digits[63]!).val ≤ 8)
    (tmp3 : EdwardsPoint)
    (tmp1 : CompletedPoint) (h_tmp1_valid : tmp1.IsValid)
    (i : Usize) (h_i : i.val ≤ 63)
    (h_inv : tmp1.toPoint =
        (I8x64_partial_radix16 scalar_digits i.val) • P.toPoint) :
    mul_loop lookup_table scalar_digits tmp3 tmp1 i ⦃ (result : CompletedPoint) =>
      result.IsValid ∧
      result.toPoint = (I8x64_partial_radix16 scalar_digits 0) • P.toPoint ⦄ := by
  unfold mul_loop
  simp only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq]
  spec_split
  · let* ⟨ i1, i1_post1, i1_post2 ⟩ ← Usize.sub_spec
    let* ⟨ tmp2, tmp2_post1, tmp2_post2 ⟩ ← CompletedPoint.as_projective_spec
    let* ⟨ tmp11, tmp11_post1, tmp11_post2 ⟩ ← ProjectivePoint.double_spec
    let* ⟨ tmp21, tmp21_post1, tmp21_post2 ⟩ ← CompletedPoint.as_projective_spec
    let* ⟨ tmp12, tmp12_post1, tmp12_post2 ⟩ ← ProjectivePoint.double_spec
    let* ⟨ tmp22, tmp22_post1, tmp22_post2 ⟩ ← CompletedPoint.as_projective_spec
    let* ⟨ tmp13, tmp13_post1, tmp13_post2 ⟩ ← ProjectivePoint.double_spec
    let* ⟨ tmp23, tmp23_post1, tmp23_post2 ⟩ ← CompletedPoint.as_projective_spec
    let* ⟨ tmp14, tmp14_post1, tmp14_post2 ⟩ ← ProjectivePoint.double_spec
    let* ⟨ tmp31, tmp31_post1, tmp31_post2, tmp31_post3, tmp31_post4, tmp31_post5, tmp31_post6,
      tmp31_post7, tmp31_post8, tmp31_post9, tmp31_post10 ⟩ ← CompletedPoint.as_extended_spec
    let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
    -- Branch-guard derivation (i > 0) and i1.val = i.val - 1 from Usize.sub_spec.
    have hi_pos : 1 ≤ i.val := by scalar_tac
    have hi1_lt_63 : i1.val < 63 := by scalar_tac
    have hi1_val : i1.val = i.val - 1 := by scalar_tac
    -- Bounds for i2 := scalar_digits[i1.val] (pulled through i2_post).
    have hi2_bds : -8 ≤ i2.val ∧ i2.val < 8 := by
      rw [i2_post]; agrind
    have hi2_lo : -8 ≤ i2.val := hi2_bds.1
    have hi2_hi : i2.val ≤ 8 := by omega
    let* ⟨ pnp, pnp_post1, pnp_post2 ⟩ ← window.LookupTable.select_spec (P := P)
    let* ⟨ tmp15, tmp15_post1, tmp15_post2 ⟩ ←
      Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add_spec
    -- Step 1 (Verus): 4 doublings = ×16. tmp14.toPoint = 16 • tmp1.toPoint (nsmul, 16 copies).
    have h14_point : tmp14.toPoint = (16 : ℕ) • tmp1.toPoint := by
      rw [tmp14_post2, tmp23_post2, tmp13_post2, tmp22_post2, tmp12_post2, tmp21_post2,
          tmp11_post2, tmp2_post2]
      abel
    -- Steps 2-5 (Verus): invariant preservation — tmp15.toPoint = partial_{i1.val} • P.toPoint.
    have h_inv_new : tmp15.toPoint =
        (I8x64_partial_radix16 scalar_digits i1.val) • P.toPoint := by
      rw [tmp15_post2, tmp31_post10, h14_point, h_inv, pnp_post2,
          ← natCast_zsmul, ← mul_smul, ← add_zsmul]
      congr 1
      rw [hi1_val, I8x64_partial_radix16_recurrence scalar_digits i.val hi_pos (by omega)]
      have h_digit : (scalar_digits[i.val - 1]!).val = i2.val := by
        rw [i2_post, show i.val - 1 = i1.val from hi1_val.symm]; simp
      rw [h_digit]
      push_cast; ring
    have hi1_le : i1.val ≤ 63 := by scalar_tac
    let* ⟨ result, result_post1, result_post2 ⟩ ← mul_loop_spec
    agrind
  · simp only [step_simps]
    agrind
termination_by i.val

end curve25519_dalek.backend.serial.scalar_mul.variable_base
