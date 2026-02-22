/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation

import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.AsBytes

-- import Curve25519Dalek/FunsExternal.lean

/-! # Spec Theorem for `ristretto.decompress.step_1`

Specification and proof for `ristretto.decompress.step_1`.

This function performs the first step of Ristretto decompression, validating
the encoding and extracting the field element s from the compressed representation.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.decompress

/-
natural language description:

    • Takes a CompressedRistretto (32-byte array) c as input
    • Extracts the (identical) byte array representation b from the compressed point c
    • Parses the bytes in b into a field element s using from_bytes b
    • Converts s back to bytes b' via to_bytes s (which always produces canonical output in [0, p))
    • Performs constant-time equality check between b and b' to determine whether the original encoding b is canonical (i.e., whether U8x32_as_Nat(b) < p)
    • Checks if s is negative (i.e., if the least significant bit of b' is 1)

      Returns a tuple containing:

        - s_encoding_is_canonical: a Choice indicating whether the input byte encoding is canonical
          (i.e., whether U8x32_as_Nat(b) < p)
        - s_is_negative: a Choice indicating whether the least significant bit of b' is equal to 1
        - s: the field element extracted from the compressed representation

    This is the first validation step in Ristretto decompression. It ensures that:

    1. The input bytes b represent a canonical field element encoding (value in [0, p))
    2. The sign/negativity of the (canonicalised) field element is determined

natural language specs:

    • The function always succeeds (no panic) for any 32-byte input c
    • s_encoding_is_canonical is true if and only if U8x32_as_Nat(c) < p
    • s_is_negative is true if and only if (Field51_as_Nat s % p) % 2 = 1
    • The output field element s is valid (i.e., its limbs are appropriately bounded)

-/


/-- **Spec for `step_1`**
Reflects the Rust implementation:
1.  Computes `s` from bytes.
2.  Computes `s_encoding_is_canonical` (checks if bytes < p).
3.  Computes `s_is_negative` (checks sign).

It proves two things:
1.  **Low-Level Correctness**: The flags match the specific bitwise conditions (`< p`, `is_negative`).
2.  **High-Level Correctness**: The function returns a valid result **iff** `decompress_step1` would return `some`.

Namely:
1. Existence: The function always succeeds
2. Safety: The resulting field element has valid limb bounds
3. Value Consistency: The field element `s` is the integer value of the bytes `c`
4. Granular Flag Meanings
5. The bridge that proves "Passing the Rust checks" iff "decompress_step1 Succeeding"
-/
@[progress]
theorem step_1_spec (c : CompressedRistretto) :
    spec (step_1 c) (fun (s_encoding_is_canonical, s_is_negative, s) =>
    s.IsValid ∧
    (s.toField = ((U8x32_as_Nat c % 2^255 : ℕ) : ZMod p)) ∧
    (s_encoding_is_canonical.val = 1#u8 ↔ U8x32_as_Nat c < p) ∧
    (s_is_negative.val = 1#u8 ↔ math.is_negative s.toField) ∧
    (ristretto.decompress_step1 c = some s.toField ↔
      (s_encoding_is_canonical.val = 1#u8 ∧ s_is_negative.val = 0#u8))) := by
  unfold step_1
  -- Step through the do-block bindings
  progress as ⟨a, ha⟩               -- as_bytes: ha : a = c
  simp only [← ha]
  progress as ⟨s, hs, hsv⟩          -- from_bytes: hs : congruence, hsv : s.IsValid
  progress as ⟨s_bytes, hbc1, hbc2⟩ -- to_bytes: hbc1 : ... ≡ ... [MOD p], hbc2 : ... < p
  -- Simplify the SliceIndexRangeFullSliceSlice index chain (identity on slices)
  simp only [core.array.Array.index, core.ops.index.IndexSlice,
    core.slice.index.Slice.index,
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
  -- Step through remaining do-block bindings
  progress as ⟨s2, hs2⟩             -- ↑(Array.to_slice c): s2 = c.to_slice
  progress as ⟨ct_flag, hct⟩        -- ct_eq: ct_flag = Choice.one ↔ s_bytes.to_slice = s2
  progress as ⟨neg_flag, hneg⟩      -- is_negative: neg_flag.val = 1#u8 ↔ ...
  -- Prove conjunction
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- s.IsValid from from_bytes_spec
    exact hsv
  · exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hs
  · -- goal: ct_flag.val = 1#u8 ↔ U8x32_as_Nat a < p
    have val_iff : ct_flag.val = 1#u8 ↔ ct_flag = Choice.one := by
      cases ct_flag; simp [Choice.one]
    subst hs2; rw [val_iff, hct]
    -- goal: s_bytes.to_slice = a.to_slice ↔ U8x32_as_Nat a < p
    have array_eq_of_slice_eq : s_bytes.to_slice = a.to_slice → s_bytes = a := by
      intro h_slice
      have h_lists : s_bytes.val = a.val := by
        have := congrArg Subtype.val h_slice
        simp [Aeneas.Std.Array.to_slice] at this; exact this
      exact Subtype.eq h_lists
    have p_lt_pow255 : p < 2 ^ 255 := Nat.sub_lt (by positivity) (by norm_num)
    constructor
    · -- forward: slices equal → U8x32_as_Nat a < p
      intro h_slice; rw [← array_eq_of_slice_eq h_slice]; exact hbc2
    · -- backward: U8x32_as_Nat a < p → slices equal
      intro h_lt
      have h_lt_255 : U8x32_as_Nat a < 2 ^ 255 := lt_trans h_lt p_lt_pow255
      have h_cong : U8x32_as_Nat s_bytes ≡ U8x32_as_Nat a [MOD p] := by
        have := hbc1.trans hs; rwa [Nat.mod_eq_of_lt h_lt_255] at this
      rw [Nat.ModEq] at h_cong
      have h_nat_eq : U8x32_as_Nat s_bytes = U8x32_as_Nat a := by
        rw [Nat.mod_eq_of_lt hbc2, Nat.mod_eq_of_lt h_lt] at h_cong; exact h_cong
      simp [U8x32_as_Nat_injective h_nat_eq]
  · simp only [math.is_negative, backend.serial.u64.field.FieldElement51.toField, beq_iff_eq]
    exact hneg
  · -- forward bridge: decompress_step1 a = some s.toField → flags
    intro h_dec
    simp only [decompress_step1] at h_dec
    split_ifs at h_dec with h_cond
    -- pos case (none = some) auto-closed; neg case remains:
    rw [Bool.or_eq_true, not_or] at h_cond
    obtain ⟨h1, h2⟩ := h_cond
    rw [decide_eq_true_eq, not_le] at h1
    rw [bne_iff_ne, not_not] at h2
    have p_lt_pow255 : p < 2 ^ 255 := Nat.sub_lt (by positivity) (by norm_num)
    have h_lt_255 : U8x32_as_Nat a < 2 ^ 255 := lt_trans h1 p_lt_pow255
    have h_arr_eq : s_bytes = a := by
      have h_cong : U8x32_as_Nat s_bytes ≡ U8x32_as_Nat a [MOD p] := by
        have := hbc1.trans hs; rwa [Nat.mod_eq_of_lt h_lt_255] at this
      have h_nat_eq : U8x32_as_Nat s_bytes = U8x32_as_Nat a := by
        rw [Nat.ModEq, Nat.mod_eq_of_lt hbc2, Nat.mod_eq_of_lt h1] at h_cong; exact h_cong
      exact U8x32_as_Nat_injective h_nat_eq
    constructor
    · -- ct_flag.val = 1#u8
      have val_iff : ct_flag.val = 1#u8 ↔ ct_flag = Choice.one := by
        cases ct_flag; simp [Choice.one]
      rw [val_iff]; subst hs2; rw [hct, h_arr_eq]
    · -- neg_flag.val = 0#u8
      have h_mod_eq : Field51_as_Nat s % p = U8x32_as_Nat a := by
        have : Field51_as_Nat s ≡ U8x32_as_Nat a [MOD p] := by
          have := hs; rwa [Nat.mod_eq_of_lt h_lt_255] at this
        rw [Nat.ModEq, Nat.mod_eq_of_lt h1] at this; exact this
      have h_not_neg : ¬(neg_flag.val = 1#u8) := by
        rw [hneg, h_mod_eq, h2]; decide
      cases neg_flag.valid with
      | inl h => exact h
      | inr h => exact absurd h h_not_neg
  · -- backward bridge: flags → decompress_step1 a = some s.toField
    intro ⟨h_ct, h_neg⟩
    -- Derive U8x32_as_Nat a < p from h_ct (via round-trip: ct_flag → s_bytes = a → hbc2)
    have h_lt : U8x32_as_Nat a < p := by
      have val_iff : ct_flag.val = 1#u8 ↔ ct_flag = Choice.one := by
        cases ct_flag; simp [Choice.one]
      subst hs2
      have h_slice_eq := hct.mp (val_iff.mp h_ct)
      have h_arr_eq : s_bytes = a := by
        have h_lists : s_bytes.val = a.val := by
          have := congrArg Subtype.val h_slice_eq
          simp [Aeneas.Std.Array.to_slice] at this; exact this
        exact Subtype.eq h_lists
      rw [← h_arr_eq]; exact hbc2
    have p_lt_pow255 : p < 2 ^ 255 := Nat.sub_lt (by positivity) (by norm_num)
    have h_lt_255 : U8x32_as_Nat a < 2 ^ 255 := lt_trans h_lt p_lt_pow255
    -- Derive U8x32_as_Nat a % 2 = 0 from h_neg (via parity chain)
    have h_even : U8x32_as_Nat a % 2 = 0 := by
      have h_not_neg : ¬(neg_flag.val = 1#u8) := by rw [h_neg]; decide
      have h_mod_eq : Field51_as_Nat s % p = U8x32_as_Nat a := by
        have : Field51_as_Nat s ≡ U8x32_as_Nat a [MOD p] := by
          have := hs; rwa [Nat.mod_eq_of_lt h_lt_255] at this
        rw [Nat.ModEq, Nat.mod_eq_of_lt h_lt] at this; exact this
      have h_parity_ne_1 : ¬(Field51_as_Nat s % p % 2 = 1) := mt hneg.mpr h_not_neg
      rw [h_mod_eq] at h_parity_ne_1; omega
    -- Show decompress_step1 a = some s.toField
    simp only [decompress_step1]
    split_ifs with h_cond
    · exfalso
      rw [Bool.or_eq_true] at h_cond
      rcases h_cond with h | h
      · rw [decide_eq_true_eq] at h; exact absurd h (not_le.mpr h_lt)
      · rw [bne_iff_ne] at h; exact absurd h_even h
    · -- value match: (↑(U8x32_as_Nat a) : ZMod p) = s.toField
      have h_cong : Field51_as_Nat s ≡ U8x32_as_Nat a [MOD p] := by
        have := hs; rwa [Nat.mod_eq_of_lt h_lt_255] at this
      simp only [Option.some.injEq, backend.serial.u64.field.FieldElement51.toField]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h_cong.symm

end curve25519_dalek.ristretto.decompress
