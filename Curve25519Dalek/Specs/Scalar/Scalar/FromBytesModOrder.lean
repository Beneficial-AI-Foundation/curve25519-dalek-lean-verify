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

Source: curve25519-dalek/src/scalar.rs -/

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
/-- If the natural number represented by a byte array is less than `L`, then the high bit (bit 7 of
byte 31) must be `0`. This is because `L < 2^255`. -/
theorem high_bit_zero_of_lt_L (bytes : Array U8 32#usize) (h : U8x32_as_Nat bytes < L) :
    bytes.val[31]!.val >>> 7 = 0 := by
  -- If the high bit were `1`, then `2^255 ≤ U8x32_as_Nat bytes`
  by_contra hc
  rw [Nat.shiftRight_eq_div_pow] at hc
  have : U8x32_as_Nat bytes ≥ 2^255 := by
    have h_eq : (bytes[31]!).val = bytes.val[31]!.val := by simp
    unfold U8x32_as_Nat
    calc U8x32_as_Nat bytes
      _ ≥ 2^(8 * 31) * (bytes[31]!).val := by
          have : 31 ∈ Finset.range 32 := by simp
          exact Finset.single_le_sum
            (fun i _ => by positivity : ∀ i ∈ Finset.range 32, 0 ≤ 2^(8 * i) * (bytes[i]!).val) this
      _ = 2^248 * (bytes[31]!).val := by norm_num
      _ ≥ 2^255 := by grind
  have : L < 2^255 := by unfold L; norm_num
  omega

/-- **Spec and proof concerning `scalar.Scalar.from_bytes_mod_order`**:
- No panic (always returns successfully)
- The result scalar s, when converted to nat, equals the input bytes converted to nat modulo L
- The result scalar s is less than L (the group order) -/
@[progress]
theorem from_bytes_mod_order_spec (b : Array U8 32#usize) :
    ∃ s, from_bytes_mod_order b = ok s ∧
    U8x32_as_Nat s.bytes ≡ U8x32_as_Nat b [MOD L] ∧ U8x32_as_Nat s.bytes < L := by
  unfold from_bytes_mod_order scalar.Indexcurve25519_dalekscalarScalarUsizeU8.index
  progress*
  have := high_bit_zero_of_lt_L s.bytes
  simp [*] at *
  grind

end curve25519_dalek.scalar.Scalar
