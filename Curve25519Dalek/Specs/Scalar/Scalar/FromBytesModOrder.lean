/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Scalar.Scalar.Reduce

/-! # Spec Theorem for `Scalar::from_bytes_mod_order`

Specification and proof for `Scalar::from_bytes_mod_order`.

This function constructs a scalar from bytes, reducing modulo the group order.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Converts a [u8;32] array a into a Scalar, then takes the modulus
      with respect to the group order \ell, and then returns the
      reduced Scalar (mod \ell) which we name s.

natural language specs:

    • scalar_to_nat(s) = (u8x32_to_nat(a) mod \ell)
    • scalar_to_nat(s) < \ell
-/

set_option maxHeartbeats 400000 in
-- Increased heartbeats needed for Finset.single_le_sum application
/-- If the natural number represented by a byte array is less than L, then the high bit (bit 7 of
byte 31) must be 0. This is because L < 2^255. -/
theorem high_bit_zero_of_lt_L (bytes : Array U8 32#usize) (h : U8x32_as_Nat bytes < L) :
    bytes.val[31]!.val >>> 7 = 0 := by
  -- Strategy: If the high bit were 1, then U8x32_as_Nat bytes >= 2^255
  -- But L < 2^255, so this contradicts h
  by_contra h_not_zero
  rw [Nat.shiftRight_eq_div_pow] at h_not_zero
  -- Get bound on byte value: it's less than 256
  have h_byte_bound : bytes.val[31]!.val < 256 := by
    have h1 := UScalar.hBounds bytes.val[31]!
    simp only at h1
    convert h1 using 2
  -- The high bit (byte / 128) is at most 1
  have h_bit_le : bytes.val[31]!.val / 2^7 ≤ 1 := by
    calc bytes.val[31]!.val / 2^7
        ≤ 255 / 2^7 := Nat.div_le_div_right (by omega : bytes.val[31]!.val ≤ 255)
      _ = 1 := by norm_num
  -- But it's not 0, so it must be exactly 1
  have h_bit_one : bytes.val[31]!.val / 2^7 = 1 := by omega
  -- If byte / 128 = 1, then byte >= 128
  have h_byte31_ge : bytes.val[31]!.val ≥ 128 := by
    have : 1 ≤ bytes.val[31]!.val / 2^7 := by omega
    have div_mod := Nat.div_add_mod bytes.val[31]!.val (2^7)
    calc bytes.val[31]!.val
        = 2^7 * (bytes.val[31]!.val / 2^7) + bytes.val[31]!.val % 2^7 := by omega
      _ ≥ 2^7 * 1 + 0 := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul_left _ this
          · exact Nat.zero_le _
      _ = 128 := by norm_num
  -- Now we need to show that this means U8x32_as_Nat bytes >= 2^255
  -- The key is that byte 31 contributes at least 128 * 2^248 = 2^255
  have h_large : U8x32_as_Nat bytes ≥ 2^255 := by
    -- Establish that the two notations refer to the same value
    have h_eq : (bytes[31]!).val = bytes.val[31]!.val := by
      conv_lhs => rw [Array.getElem!_Nat_eq]
    -- Byte 31 alone contributes at least 128 * 2^248
    have h31_contrib : 2^248 * bytes.val[31]!.val ≥ 2^255 := by
      calc 2^248 * bytes.val[31]!.val
          ≥ 2^248 * 128 := Nat.mul_le_mul_left _ h_byte31_ge
        _ = 2^255 := by norm_num
    -- U8x32_as_Nat bytes is at least as large as the contribution from byte 31
    unfold U8x32_as_Nat
    calc U8x32_as_Nat bytes
        = ∑ i ∈ Finset.range 32, 2^(8 * i) * (bytes[i]!).val := rfl
      _ ≥ 2^(8 * 31) * (bytes[31]!).val := by
          have : 31 ∈ Finset.range 32 := by simp
          exact Finset.single_le_sum (fun i _ => by positivity : ∀ i ∈ Finset.range 32, 0 ≤ 2^(8 * i) * (bytes[i]!).val) this
      _ = 2^248 * (bytes[31]!).val := by norm_num
      _ ≥ 2^248 * bytes.val[31]!.val := by rw [← h_eq]
      _ ≥ 2^255 := h31_contrib
  -- But L < 2^255, contradicting h
  have h_L_bound : L < 2^255 := by unfold L; norm_num
  omega

/-- **Spec and proof concerning `scalar.Scalar.from_bytes_mod_order`**:
- No panic (always returns successfully)
- The result scalar s, when converted to nat, equals the input bytes converted to nat modulo L
- The result scalar s is less than L (the group order) -/
@[progress]
theorem from_bytes_mod_order_spec (b : Array U8 32#usize) :
    ∃ s, from_bytes_mod_order b = ok s ∧
    U8x32_as_Nat s.bytes ≡ U8x32_as_Nat b [MOD L] ∧
    U8x32_as_Nat s.bytes < L := by
  unfold from_bytes_mod_order scalar.Indexcurve25519_dalekscalarScalarUsizeU8.index
  progress*
  have := high_bit_zero_of_lt_L s.bytes
  simp [*] at *
  grind

end curve25519_dalek.scalar.Scalar
