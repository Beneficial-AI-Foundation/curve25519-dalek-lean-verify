/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add
import Curve25519Dalek.Specs.Backend.Serial.ScalarMul.VariableBase.MulLoop
import Curve25519Dalek.Specs.Window.LookupTable.From
import Curve25519Dalek.Specs.Window.LookupTable.Select
import Curve25519Dalek.Specs.Scalar.Scalar.AsRadix16
import Curve25519Dalek.Specs.Scalar.Scalar.AsRadix2w
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.ExternallyVerified
import Mathlib

/-! # Spec Theorem for `variable_base::mul`

Top-level constant-time variable-base scalar multiplication. Builds a lookup table
from `point`, decomposes `scalar` into radix-16 signed digits, unrolls the first
loop iteration (for digit 63), then runs `mul_loop` for the remaining 63 iterations,
and finally converts back to `EdwardsPoint`.

**Source**: curve25519-dalek/src/backend/serial/scalar_mul/variable_base.rs, lines 11-51
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.edwards curve25519_dalek.scalar curve25519_dalek.scalar.Scalar

namespace curve25519_dalek.backend.serial.scalar_mul.variable_base

/-- Local bound-tightening lemma: given the weak spec output of `as_radix_16`
(with the `s_63 ≤ 16` postcondition) plus the scalar invariant `U8x32_as_Nat < 2^255`,
derive the tighter bound `s_63 ≤ 8` needed by `select_spec`.

Argument: `s_63 * 16^63 + ∑_{i<63} 16^i * s_i = V < 2^255 = 8 * 16^63`.
Lower-bounding the inner sum by `-8 * (16^63 - 1)/15`, multiplying by 15, and
combining gives `15 * s_63 * 16^63 < 128 * 16^63`, hence `s_63 ≤ 8`. -/
private lemma scalar_digit_63_le_8
    (digits : Array Std.I8 64#usize)
    (V : ℕ)
    (h_val : I8x64_as_Radix16 digits = (V : ℤ))
    (h_V_lt : V < 2 ^ 255)
    (h_inner : ∀ i < 63, -8 ≤ (digits[i]!).val ∧ (digits[i]!).val < 8) :
    (digits[63]!).val ≤ 8 := by
  by_contra h_neg
  push_neg at h_neg
  have h_s63_ge_9 : 9 ≤ (digits[63]!).val := h_neg
  -- Split the full sum: s_63 * 16^63 + ∑_{i<63} 16^i * s_i = V.
  have h_split : (digits[63]!).val * (16 : ℤ) ^ 63 +
      ∑ i ∈ Finset.range 63, (16 : ℤ) ^ i * (digits[i]!).val = V := by
    rw [← h_val]
    unfold I8x64_as_Radix16
    rw [Finset.sum_range_succ (fun i => (16 : ℤ) ^ i * (digits[i]!).val) 63]
    ring
  -- Lower bound the inner signed sum by -8 * ∑_{i<63} 16^i.
  have h_inner_lb :
      -8 * ∑ i ∈ Finset.range 63, (16 : ℤ) ^ i ≤
        ∑ i ∈ Finset.range 63, (16 : ℤ) ^ i * (digits[i]!).val := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intros i hi
    have hi63 : i < 63 := Finset.mem_range.mp hi
    have h_pow : (0 : ℤ) ≤ (16 : ℤ) ^ i := pow_nonneg (by norm_num) i
    have := (h_inner i hi63).1
    nlinarith
  -- Geometric sum: (∑_{i<63} 16^i) * (16 - 1) = 16^63 - 1.
  have h_geom : 15 * ∑ i ∈ Finset.range 63, (16 : ℤ) ^ i = (16 : ℤ) ^ 63 - 1 := by
    have := geom_sum_mul (16 : ℤ) 63
    linarith
  -- 2^255 = 8 * 16^63.
  have h_255_eq : (2 : ℤ) ^ 255 = 8 * (16 : ℤ) ^ 63 := by
    rw [show (255 : ℕ) = 3 + 4 * 63 from by norm_num, pow_add, pow_mul]
    norm_num
  have h_V_Z : (V : ℤ) < (2 : ℤ) ^ 255 := by exact_mod_cast h_V_lt
  have h_pow_pos : (0 : ℤ) < (16 : ℤ) ^ 63 := pow_pos (by norm_num) 63
  -- Derive contradiction: if s_63 ≥ 9, then 9 * 16^63 ≤ s_63 * 16^63 = V - inner_sum ≤ V + 8 * S,
  -- giving 135 * 16^63 ≤ 15V + 8(16^63 - 1) < 120 * 16^63 + 8 * 16^63 = 128 * 16^63. Contradiction.
  nlinarith [h_split, h_inner_lb, h_geom, h_V_Z, h_255_eq, h_pow_pos, h_s63_ge_9,
             mul_pos (show (0:ℤ) < 9 from by norm_num) h_pow_pos]

/-- **Spec and proof concerning `variable_base.mul`**:
- No panic (always returns successfully) given `point.IsValid` and
  `(scalar.bytes[31]!).val ≤ 127`.
- The result is a valid `EdwardsPoint`.
- It represents `(U8x32_as_Nat scalar.bytes) • point.toPoint` on Ed25519.
-/
@[step]
theorem mul_spec (point : EdwardsPoint) (hpoint : point.IsValid)
    (scalar : Scalar) (h_top : (scalar.bytes[31]!).val ≤ 127) :
    mul point scalar ⦃ (result : EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = ((U8x32_as_Nat scalar.bytes : ℕ) : ℤ) • point.toPoint ⦄ := by
  unfold mul
  -- 1. Build lookup table [P, 2P, ..., 8P].
  let* ⟨ lookup_table, h_table_valid, h_table_point ⟩ ←
    window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_spec
  -- 2. Decompose scalar into 64 signed radix-16 digits.
  let* ⟨ scalar_digits, h_val, h_inner, h_63_lo, h_63_hi ⟩ ← Scalar.as_radix_16_spec
  -- Tighten s_63 ≤ 16 → s_63 ≤ 8 using the scalar invariant.
  have h_V_lt : U8x32_as_Nat scalar.bytes < 2 ^ 255 :=
    Scalar.U8x32_as_Nat_lt_pow255 scalar h_top
  have h_s63_le_8 : (scalar_digits[63]!).val ≤ 8 :=
    scalar_digit_63_le_8 scalar_digits (U8x32_as_Nat scalar.bytes) h_val h_V_lt h_inner
  -- 3. Identity EdwardsPoint (tmp3 = 0).
  let* ⟨ tmp3, _, _, _, _, h_tmp3_valid, h_tmp3_zero ⟩ ←
    EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec
  -- 4. Read s_63.
  let* ⟨ i63, h_i63 ⟩ ← Array.index_usize_spec
  -- Derive bounds for select_spec (needs -8 ≤ i63.val ≤ 8).
  have hi63_lo : -8 ≤ i63.val := by rw [h_i63]; agrind
  have hi63_hi : i63.val ≤ 8 := by rw [h_i63]; agrind
  -- 5. Select lookup_table[s_63] = s_63 • point.
  let* ⟨ pnp, pnp_valid, pnp_point ⟩ ← window.LookupTable.select_spec (P := point)
  -- 6. Add: tmp1 = tmp3 + pnp (EdwardsPoint + PNP → CompletedPoint).
  let* ⟨ tmp1, tmp1_valid, tmp1_point ⟩ ←
    Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add_spec
  -- Establish initial invariant for mul_loop: tmp1.toPoint = partial_{63} • point.
  -- partial_{63} = ∑_{j<1} 16^j * digits[63+j]!.val = s_63.
  have h_partial_63 :
      I8x64_partial_radix16 scalar_digits 63 = (scalar_digits[63]!).val := by
    unfold I8x64_partial_radix16
    simp
  have h_tmp1_inv : tmp1.toPoint =
      (I8x64_partial_radix16 scalar_digits 63) • point.toPoint := by
    rw [tmp1_point, h_tmp3_zero, zero_add, pnp_point, h_partial_63, h_i63]
    simp
  -- 7. Run mul_loop for 63 iterations (i decreases from 63 to 0).
  let* ⟨ tmp11, tmp11_valid, tmp11_point ⟩ ← mul_loop_spec (P := point)
  -- 8. Convert final CompletedPoint back to EdwardsPoint.
  let* ⟨ result, _, _, _, _, _, _, _, _, result_valid, result_point ⟩ ←
    CompletedPoint.as_extended_spec
  refine ⟨result_valid, ?_⟩
  -- Connect: result.toPoint = tmp11.toPoint = partial_0 • point = I8x64_as_Radix16 • point
  --                        = U8x32_as_Nat • point.
  rw [result_point, tmp11_point]
  congr 1

end curve25519_dalek.backend.serial.scalar_mul.variable_base
