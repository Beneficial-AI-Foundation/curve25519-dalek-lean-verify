/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.AsMontgomery
/-! # Spec Theorem for `Scalar52::from_bytes_wide`

Specification and proof for `Scalar52::from_bytes_wide`.

This function constructs an unpacked scalar from a wide byte array.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

set_option maxHeartbeats 4000000
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes a 64-byte array b as input and returns an unpacked scalar u that
      represents the 512-bit integer value reduced modulo L, redistributed into five limbs.

natural language specs:

    • scalar_to_nat(u) = u8x64_to_nat(b) % L
-/

lemma U8x64_as_Nat_split (b : Array U8 64#usize) :
    ∃ lo4 hi4, U8x64_as_Nat b = Scalar52_as_Nat lo4 + Scalar52_as_Nat hi4 * 2^256
    ∧ (∀ i, i < 5 → (lo4[i]!).val < 2 ^ 62)
    ∧ (∀ i, i < 5 → (hi4[i]!).val < 2 ^ 62)
    := by
  unfold U8x64_as_Nat
  have b_split1: ∑ i ∈ Finset.range 64, 2 ^ (8 * i) * (b[i]!.val) =∑ i ∈ Finset.range (32 + 32), 2 ^ (8 * i) * (b[i]!.val) :=
  by grind
  have b_split: ∑ i ∈ Finset.range 64, 2 ^ (8 * i) * (b[i]!.val) =
    (∑ i ∈ Finset.range 32, 2 ^ (8 * i) * b[i]!.val) +
    (∑ i ∈ Finset.range 32, 2 ^ (8 * (i + 32)) * b[i + 32]!.val) := by
      rw [b_split1]
      rw [Finset.sum_range_add]
      grind
  have low_bits_eq: ∃ lo4, ∑ i ∈ Finset.range 32, 2 ^ (8 * i) * (b[i]!.val) = Scalar52_as_Nat lo4 ∧ (∀ i, i < 5 → (lo4[i]!).val < 2 ^ 62) := by sorry
  have high_bits_eq: ∃ hi4, ∑ i ∈ Finset.range 32, 2 ^ (8 * (i + 32)) * b[i + 32]!.val = Scalar52_as_Nat hi4 * 2^256 ∧ (∀ i, i < 5 → (hi4[i]!).val < 2 ^ 62) := by sorry
  obtain ⟨lo4, h_lo4_eq, h_lo4_range⟩ := low_bits_eq
  obtain ⟨hi4, h_hi4_eq, h_hi4_range⟩ := high_bits_eq
  grind

lemma R_lt: ∀ i, i < 5 → constants.R[i]!.val < 2 ^62 := by
  unfold constants.R
  decide
--   omega

/-- Interpret 8 consecutive bytes as a little-endian U64 value -/
def bytes_to_u64_le (bytes : Array U8 64#usize) (start : Nat) : Nat :=
  ∑ k ∈ Finset.range 8, 2^(8 * k) * (bytes[start + k]!).val

/-- Interpret an 8-element U64 array as a natural number -/
def U64x8_as_Nat (words : Array U64 8#usize) : Nat :=
  ∑ j ∈ Finset.range 8, 2^(64 * j) * (words[j]!).val

/-- **Spec for `backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop`**:
- Starting from index `i`, converts each group of 8 bytes into a U64 word
- For indices j ≥ i, the result word equals the little-endian interpretation of bytes[j*8..j*8+8]
- Words before index i are preserved
- The loop always succeeds (no panic) -/
@[progress]
theorem from_bytes_wide_loop_spec (bytes : Array U8 64#usize) (words : Array U64 8#usize) (i : Usize)
    (hi : i.val ≤ 8) :
    ∃ words', from_bytes_wide_loop bytes words i = ok words' ∧
    (∀ j, i.val ≤ j → j < 8 → words'[j]!.val = bytes_to_u64_le bytes (j * 8)) ∧
    (∀ j, j < i.val → words'[j]! = words[j]!) := by
  sorry


/-- **Spec and proof concerning `scalar.Scalar52.from_bytes_wide`**:
- No panic (always returns successfully)
- The result represents the input byte array reduced modulo L (canonical form) -/
@[progress]
theorem from_bytes_wide_spec (b : Array U8 64#usize)
(h_bounds : ∀ i, i < 8 → b[i]!.val < 2 ^ 52)
 :
    ∃ u, from_bytes_wide b = ok u ∧
    Scalar52_as_Nat u = U8x64_as_Nat b % L := by
  unfold from_bytes_wide
  unfold IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut
  progress*
  -- decide
  -- scalar_tac
  · rw [i40_post]
    decide
  · intro i hi
    have h_mask_val : mask.val = 2^52 - 1 := by
      scalar_tac
    have h_mask_lt : mask.val < 2^62 := by
      scalar_tac
    interval_cases i <;> simp
    · rw [i2_post_1]
      have h_bound : (i1 &&& mask).val ≤ mask.val := by
        bvify 64 at *
        bv_decide
      have h_final : (i1 &&& mask).val < 2^62 := by
        linarith [h_bound, h_mask_lt]
      exact h_final
    · rw [i7_post_1]
      have h_bound : (i6&&& mask).val ≤ mask.val := by
        bvify 64 at *
        bv_decide
      have h_final : (i6 &&& mask).val < 2^62 := by
        linarith [h_bound, h_mask_lt]
      exact h_final
    · rw [i12_post_1]
      have h_bound : (i11&&& mask).val ≤ mask.val := by
        bvify 64 at *
        bv_decide
      have h_final : (i11 &&& mask).val < 2^62 := by
        linarith [h_bound, h_mask_lt]
      exact h_final
    · rw [i17_post_1]
      have h_bound : (i16&&& mask).val ≤ mask.val := by
        bvify 64 at *
        bv_decide
      have h_final : (i16 &&& mask).val < 2^62 := by
        linarith [h_bound, h_mask_lt]
      exact h_final
    · rw [i22_post_1]
      have h_bound : (i21&&& mask).val ≤ mask.val := by
        bvify 64 at *
        bv_decide
      have h_final : (i21 &&& mask).val < 2^62 := by
        linarith [h_bound, h_mask_lt]
      exact h_final
  · unfold constants.R
    decide
  · intro i hi
    have h_mask_val : mask.val = 2^52 - 1 := by
      scalar_tac
    have h_mask_lt : mask.val < 2^62 := by
      scalar_tac
    interval_cases i <;> simp
    · rw [i24_post_1]
      have h_bound : (i23&&& mask).val ≤ mask.val := by
        bvify 64 at *
        bv_decide
      have h_final : (i23 &&& mask).val < 2^62 := by
        linarith [h_bound, h_mask_lt]
      exact h_final
    · rw [i29_post_1]
      have h_bound : (i28&&& mask).val ≤ mask.val := by
        bvify 64 at *
        bv_decide
      have h_final : (i28 &&& mask).val < 2^62 := by
        linarith [h_bound, h_mask_lt]
      exact h_final
    · rw [i34_post_1]
      have h_bound : (i33&&& mask).val ≤ mask.val := by
        bvify 64 at *
        bv_decide
      have h_final : (i33 &&& mask).val < 2^62 := by
        linarith [h_bound, h_mask_lt]
      exact h_final
    · rw [i39_post_1]
      have h_bound : (i38&&& mask).val ≤ mask.val := by
        bvify 64 at *
        bv_decide
      have h_final : (i38 &&& mask).val < 2^62 := by
        linarith [h_bound, h_mask_lt]
      exact h_final
    · rw [i41_post_1]
      scalar_tac
  · unfold constants.RR
    decide
  · let lo := (((((Aeneas.Std.Array.set ZERO 0#usize i2).set 1#usize i7).set 2#usize i12).set
    3#usize i17).set 4#usize i22)
    let hi := (((((Aeneas.Std.Array.set ZERO 0#usize i24).set 1#usize i29).set 2#usize i34).set 3#usize i39).set 4#usize i41)


    have h_b_decomp : U8x64_as_Nat b = Scalar52_as_Nat lo + Scalar52_as_Nat hi * R := by
      sorry
    -- grind []

    have h_combined : Scalar52_as_Nat hi5 + Scalar52_as_Nat lo5 = (Scalar52_as_Nat hi * R + Scalar52_as_Nat lo) := by
      sorry

    grind

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
