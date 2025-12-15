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
theorem from_bytes_wide_spec (b : Array U8 64#usize) :
    ∃ u, from_bytes_wide b = ok u ∧
    Scalar52_as_Nat u = U8x64_as_Nat b % L := by
  unfold from_bytes_wide
  unfold IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut
  progress*
  -- decide
  -- scalar_tac
  · rw [i40_post]
    decide
  · sorry
  · sorry
  · sorry
  · unfold constants.RR
    decide
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry


  -- -- U8x64_as_Nat b = lo_nat + hi_nat * 2^256
  -- have h_lo_hi: ∃ lo hi, U8x64_as_Nat b = Scalar52_as_Nat lo + Scalar52_as_Nat hi * 2^256
  -- ∧ (∀ i, i < 5 → (lo[i]!).val < 2 ^ 62) ∧ (∀ i, i < 5 → (hi[i]!).val < 2 ^ 62)
  --  := U8x64_as_Nat_split b
  -- obtain ⟨lo, hi, h_lo_hi, lo_range, hi_range⟩ := h_lo_hi
  -- -- (lo * R) / R = lo2
  -- obtain ⟨lo2, h_lo2_ok, h_lo2_spec⟩ := montgomery_mul_spec lo constants.R (lo_range) (R_lt)
  -- -- (hi * R^2) / R = hi2
  -- obtain ⟨hi2, h_hi2_ok, h_hi2_spec⟩ := montgomery_mul_spec hi constants.RR (hi_range) (RR_lt)

  -- -- (hi * R^2) / R + (lo * R) / R = u
  -- -- True according to line 128 - line 131 in curve25519-dalek/src/backend/serial/u64/scalar.rs
  -- obtain ⟨u, h_u_ok, h_u_spec⟩ := add_spec (hi2) (lo2)

  -- -- Keypoint:2^256 * R ≡ R^2 [MOD L]
  -- have h_key : 2^256 * R % L = R^2 % L := by
  --   unfold R
  -- -- 2^256 * 2^260 = 2^516
  -- -- R^2 = (2^260)^2 = 2^520
  -- -- need to prove 2^516 % L = 2^520 % L
  --   sorry
  -- use u
  -- constructor
  -- · -- from_bytes_wide b = ok u
  --   -- True by the definition of from_bytes_wide_spec
  --   sorry
  -- · -- Scalar52_as_Nat u = U8x64_as_Nat b % L
  --   rw [h_u_spec]
  --   rw [h_lo_hi]

  --   sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
