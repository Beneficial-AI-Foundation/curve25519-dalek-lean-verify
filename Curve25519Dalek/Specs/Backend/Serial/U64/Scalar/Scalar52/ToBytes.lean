/-
Copyright 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Lim Jin Xing, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.BitList

/-!
# Spec Theorem for `Scalar52::to_bytes`

This function converts a `Scalar52` to its byte representation.

Source: "curve25519-dalek/src/backend/serial/u64/scalar.rs"

## Rust Source

```rust
/// Pack the limbs of this `Scalar52` into 32 bytes
pub fn to_bytes(self) -> [u8; 32] {
    let mut s = [0u8; 32];

    s[ 0] = (self.0[ 0] >> 0) as u8;
    s[ 1] = (self.0[ 0] >> 8) as u8;
    s[ 2] = (self.0[ 0] >> 16) as u8;
    s[ 3] = (self.0[ 0] >> 24) as u8;
    s[ 4] = (self.0[ 0] >> 32) as u8;
    s[ 5] = (self.0[ 0] >> 40) as u8;
    s[ 6] = ((self.0[ 0] >> 48) | (self.0[ 1] << 4)) as u8;
    s[ 7] = (self.0[ 1] >> 4) as u8;
    s[ 8] = (self.0[ 1] >> 12) as u8;
    s[ 9] = (self.0[ 1] >> 20) as u8;
    s[10] = (self.0[ 1] >> 28) as u8;
    s[11] = (self.0[ 1] >> 36) as u8;
    s[12] = (self.0[ 1] >> 44) as u8;
    s[13] = (self.0[ 2] >> 0) as u8;
    s[14] = (self.0[ 2] >> 8) as u8;
    s[15] = (self.0[ 2] >> 16) as u8;
    s[16] = (self.0[ 2] >> 24) as u8;
    s[17] = (self.0[ 2] >> 32) as u8;
    s[18] = (self.0[ 2] >> 40) as u8;
    s[19] = ((self.0[ 2] >> 48) | (self.0[ 3] << 4)) as u8;
    s[20] = (self.0[ 3] >> 4) as u8;
    s[21] = (self.0[ 3] >> 12) as u8;
    s[22] = (self.0[ 3] >> 20) as u8;
    s[23] = (self.0[ 3] >> 28) as u8;
    s[24] = (self.0[ 3] >> 36) as u8;
    s[25] = (self.0[ 3] >> 44) as u8;
    s[26] = (self.0[ 4] >> 0) as u8;
    s[27] = (self.0[ 4] >> 8) as u8;
    s[28] = (self.0[ 4] >> 16) as u8;
    s[29] = (self.0[ 4] >> 24) as u8;
    s[30] = (self.0[ 4] >> 32) as u8;
    s[31] = (self.0[ 4] >> 40) as u8;

    s
}
```

## Bit layout

Each limb holds 52 bits. Since 52 = 6×8 + 4, each limb fills 6 full bytes plus 4 bits that
spill into a shared byte with the adjacent limb. The two shared bytes are s[6] and s[19],
constructed via OR of the overflow bits from one limb and the start bits of the next.

  | Limb | Bits | Bytes                              | Shared |
  |------|------|------------------------------------|--------|
  |  0   | 0–51 | s[0]–s[5], lower nibble of s[6]    | s[6]   |
  |  1   | 0–51 | upper nibble of s[6], s[7]–s[12]   | s[6]   |
  |  2   | 0–51 | s[13]–s[18], lower nibble of s[19] | s[19]  |
  |  3   | 0–51 | upper nibble of s[19], s[20]–s[25] | s[19]  |
  |  4   | 0–47 | s[26]–s[31] (48 bits)              | none   |

Limb 4 uses only 48 of its 52 bits because the precondition `Scalar52_as_Nat self < L < 2^253`
implies `self[4] < 2^(253−208) = 2^45 < 2^48`.

Total: limbs hold 5×52 = 260 bits, but the value fits in 32×8 = 256 bits.

## Proof overview

We express each of the 32 byte assignments as a `BitList.extract` equality, use
`List.extract_append_extract` to merge adjacent extracts into limb-level equivalences,
then convert to `Nat` via `toNat` and close with `grind`.
-/


open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52
open List BitList
attribute [local simp] Array.length_eq

/-! ## BitList spec theorems for scalar operations

These theorems express the four key operations (shift right, cast U64→U8, shift left, bitwise OR)
in terms of `BitList` operations.

They mirror the Nat-level spec theorems from Aeneas but with BitList postconditions:
- Right shift by k ↔ `drop k` (plus zero padding at top)
- Cast U64→U8 ↔ `take 8`
- Left shift by k ↔ `replicate k false ++` (plus truncation)
- Bitwise OR (non-overlapping) ↔ concatenation of `take`/`drop` slices
-/

/-- Concatenating adjacent extracts yields the combined extract. -/
theorem List.extract_append_extract {α : Type*} (l : List α) (a b c : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) :
    l.extract a b ++ l.extract b c = l.extract a c := by
  simp only [List.extract_eq_drop_take]
  conv_rhs => rw [show c - a = (b - a) + (c - b) from by omega]
  rw [List.take_add]
  congr 1
  rw [List.drop_drop, show a + (b - a) = b from by omega]

private lemma testBit_add_mul_pow_low (b q k i : Nat) (hb : b < 2 ^ k) (hi : i < k) :
    (b + 2^k * q).testBit i = b.testBit i := by
  have h1 : (b + 2^k * q) % 2^k = b := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have h2 := Nat.testBit_mod_two_pow (b + 2^k * q) k i
  rw [h1] at h2; simp [hi] at h2; exact h2.symm

private lemma testBit_add_mul_pow_high (b q k i : Nat) (hb : b < 2 ^ k) (hi : k ≤ i) :
    (b + 2^k * q).testBit i = (2^k * q).testBit i := by
  set n := i - k
  have hi_eq : i = n + k := by omega
  rw [hi_eq, Nat.testBit_add, Nat.testBit_add]
  congr 1
  rw [Nat.add_mul_div_left _ _ (by positivity : (0 : Nat) < 2^k),
      Nat.div_eq_of_lt hb, Nat.zero_add,
      Nat.mul_div_cancel_left _ (by positivity : (0 : Nat) < 2^k)]

/-- Non-overlapping OR equals addition: if `a` has zeros in the bottom `k` bits
    and `b` fits in `k` bits, then `a ||| b = a + b`. -/
private theorem nat_or_eq_add (a b k : Nat) (ha : a % 2 ^ k = 0) (hb : b < 2 ^ k) :
    a ||| b = a + b := by
  have ha_low : ∀ j, j < k → a.testBit j = false := by
    intro j hj
    have h1 := Nat.testBit_mod_two_pow a k j
    rw [ha] at h1; simp_all
  have hb_high : ∀ j, j ≥ k → b.testBit j = false := by
    intro j hj
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hj))
  have ha_eq : a = 2^k * (a / 2^k) := by have := Nat.div_add_mod a (2^k); omega
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  by_cases hi : i < k
  · rw [ha_low i hi, Bool.false_or, ha_eq, Nat.add_comm]
    exact (testBit_add_mul_pow_low b (a / 2^k) k i hb hi).symm
  · rw [hb_high i (by omega), Bool.or_false, ha_eq, Nat.add_comm]
    exact (testBit_add_mul_pow_high b (a / 2^k) k i hb (by omega)).symm

/-- `ofNat k 0 = replicate k false` (all-zeros bit list). -/
private theorem ofNat_zero (w : Nat) : ofNat w 0 = List.replicate w false := by
  induction w with
  | zero => simp [ofNat]
  | succ w ih => simp [ofNat, ih, List.replicate_succ]

/-- `toNat (replicate k false) = 0`. -/
private theorem toNat_replicate_false (k : Nat) : toNat (List.replicate k false) = 0 := by
  induction k with
  | zero => simp [toNat]
  | succ k ih => simp [List.replicate_succ, toNat, ih]

/-- If the bottom `k` bits of a U64 are all false (from a shift-left), then `val % 2^k = 0`. -/
private theorem val_mod_of_replicate_prefix (x : U64) (k : Nat) (rest : List Bool)
    (hx : ofU64 x = List.replicate k false ++ rest) : x.val % 2 ^ k = 0 := by
  have := congr_arg toNat hx
  grind [Nat.mul_comm, Nat.mul_mod_right, toNat_ofU64, toNat_append, toNat_replicate_false]

/-- If a U64 is a right-shift of `y` by `shift` bits and `y < 2^(shift+bits)`, then `x < 2^bits`. -/
private theorem val_lt_of_shift_right (x y : U64) (shift bits : Nat)
    (hx : ofU64 x = (ofU64 y).drop shift ++ List.replicate shift false)
    (hy : y.val < 2 ^ (shift + bits)) : x.val < 2 ^ bits := by
  have h := congr_arg toNat hx
  rw [toNat_ofU64, toNat_append, toNat_drop, toNat_ofU64,
    toNat_replicate_false, length_drop, ofU64_length] at h
  simp only [Nat.zero_mul, Nat.add_zero] at h
  rw [h]; exact Nat.div_lt_of_lt_mul (by rwa [← Nat.pow_add])

/-- Right-shifting a U64 by `k` drops the bottom `k` bits (`BitList` spec). -/
theorem U64.ShiftRight_IScalar_bitList_spec {ty1} (x : U64) (y : IScalar ty1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val < 64) :
    (x >>> y) ⦃ (z : UScalar UScalarTy.U64) =>
      ofU64 z = (ofU64 x).drop y.toNat ++ List.replicate y.toNat false ⦄ := by
  have hk : y.toNat < 64 := by scalar_tac
  have hx64 : x.val < 2 ^ 64 := x.hmax
  have h := U64.ShiftRight_IScalar_spec x y hy0 hy1
  exact WP.spec_mono h fun z ⟨hval, _⟩ => by
    change ofNat 64 z.val = (ofNat 64 x.val).drop y.toNat ++ List.replicate y.toNat false
    rw [hval, Nat.shiftRight_eq_div_pow, ofNat_drop y.toNat 64 x.val (by omega)]
    have hlt : x.val / 2 ^ y.toNat < 2 ^ (64 - y.toNat) :=
      Nat.div_lt_of_lt_mul (by
        have : 2 ^ y.toNat * 2 ^ (64 - y.toNat) = 2 ^ 64 := by
          rw [← Nat.pow_add]; congr 1; omega
        linarith)
    conv_lhs => rw [show (64 : Nat) = (64 - y.toNat) + y.toNat from by omega]
    rw [ofNat_split (64 - y.toNat) y.toNat (x.val / 2 ^ y.toNat)]
    congr 1
    rw [Nat.div_eq_of_lt hlt, ofNat_zero]

-- TODO: move to BitList file
/-- Casting a U64 to U8 takes the bottom 8 bits. -/
@[simp]
theorem ofU8_cast_eq_ofU64_take (x : U64) : ofU8 (UScalar.cast .U8 x) = (ofU64 x).take 8 := by
  change ofNat 8 (UScalar.cast .U8 x).val = (ofNat 64 x.val).take 8
  rw [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, ofNat_mod, ofNat_take 8 64 x.val (by omega)]

/-- Left-shifting a U64 by `k` prepends `k` zero bits at the bottom and truncates to 64 bits. -/
theorem U64.ShiftLeft_IScalar_bitList_spec {ty1} (x : U64) (y : IScalar ty1)
    (hy : 0 ≤ y.val) (hy' : y.val < 64) :
    (x <<< y) ⦃ (z : UScalar UScalarTy.U64) =>
      ofU64 z = List.replicate y.toNat false ++ (ofU64 x).take (64 - y.toNat) ⦄ := by
  have : y.toNat < 64 := by scalar_tac
  have h := U64.ShiftLeft_IScalar_spec x y hy hy'
  exact WP.spec_mono h fun z ⟨hval, _⟩ => by
    change ofNat 64 z.val = List.replicate y.toNat false ++ (ofNat 64 x.val).take (64 - y.toNat)
    rw [hval, Nat.shiftLeft_eq]
    have hsize : U64.size = 2 ^ 64 := by scalar_tac
    rw [hsize, ofNat_mod]
    conv_lhs => rw [show (64 : Nat) = y.toNat + (64 - y.toNat) from by omega]
    rw [ofNat_split y.toNat (64 - y.toNat) (x.val * 2 ^ y.toNat)]
    congr 1
    · -- Bottom k bits of x.val * 2^k are all zero
      conv_lhs => rw [← ofNat_mod y.toNat (x.val * 2 ^ y.toNat)]
      rw [Nat.mul_comm, Nat.mul_mod_right, ofNat_zero]
    · -- Upper bits are just x.val
      rw [Nat.mul_div_cancel _ (by positivity)]
      exact (ofNat_take (64 - y.toNat) 64 x.val (by omega)).symm

/-- Bitwise OR on non-overlapping values: if `x` has zeros in the bottom `k` bits and `y` fits in
`k` bits, then OR concatenates the respective bit slices. -/
theorem ofU64_or_non_overlapping (x y : U64) (k : Nat) (hk : k ≤ 64)
    (hx : x.val % 2 ^ k = 0) (hy : y.val < 2 ^ k) :
    ofU64 (x ||| y) = (ofU64 y).take k ++ (ofU64 x).drop k := by
  have hor_eq : (x ||| y).val = x.val + y.val := by
    simp only [UScalar.val_or]
    exact nat_or_eq_add x.val y.val k hx hy
  change ofNat 64 (x ||| y).val = (ofNat 64 y.val).take k ++ (ofNat 64 x.val).drop k
  rw [hor_eq, show x.val + y.val = y.val + 2 ^ k * (x.val / 2 ^ k) from by
    have := Nat.div_add_mod x.val (2 ^ k); omega]
  conv_lhs => rw [show (64 : Nat) = k + (64 - k) from by omega]
  rw [ofNat_split k (64 - k)]
  congr 1
  · conv_lhs => rw [← ofNat_mod k (y.val + 2 ^ k * (x.val / 2 ^ k))]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
    exact (ofNat_take k 64 y.val (by omega)).symm
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hy, Nat.zero_add]
    exact (ofNat_drop k 64 x.val (by omega)).symm

/-- Convert an OR `bv` postcondition (as produced by `progress` on `lift (x ||| y)`) into BitList
form, given non-overlap preconditions. -/
private theorem ofU64_of_or_bv (x y z : U64) (k : Nat) (hk : k ≤ 64) (hx : x.val % 2 ^ k = 0)
    (hy : y.val < 2 ^ k) (hbv : z.bv = y.bv ||| x.bv) :
    ofU64 z = (ofU64 y).take k ++ (ofU64 x).drop k := by
  have heq : z = x ||| y := by
    have : z.bv = (x ||| y).bv := by
      rw [hbv, UScalar.bv_or]; ext i; simp [Bool.or_comm]
    have := congrArg BitVec.toNat this; scalar_tac
  rw [heq]; exact ofU64_or_non_overlapping x y k hk hx hy

-- TODO: this is a strengthening of `Scalar52_top_limb_lt_of_as_Nat_lt` in Aux.lean (which gives
-- < 2^51 from < 2^259). This tighter bound should be moved to the central location.
/-- If `Scalar52_as_Nat a < L`, then the top limb `a[4]` is bounded by `2^45`.
This follows because `2^208 * a[4] ≤ Scalar52_as_Nat a < L < 2^253`. -/
theorem Scalar52_top_limb_lt_of_canonical (a : Array U64 5#usize) (h : Scalar52_as_Nat a < L) :
  (a : List U64)[4]!.val < 2 ^ 45 := by
  unfold Scalar52_as_Nat at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  have : L < 2 ^ 253 := by unfold L; omega
  grind

/-- At a shared byte (s[6] or s[19]), the lower and upper nibble contributions recombine:
    `(x % 2^4) * 2^a + (x / 2^4) * 2^(a+4) = x * 2^a`. -/
private theorem shared_byte_recombine (x a : Nat) :
    (x % 2 ^ 4) * 2 ^ a + (x / 2 ^ 4) * 2 ^ (a + 4) = x * 2 ^ a := by
  conv_lhs => rw [show (2 : Nat) ^ (a + 4) = 2 ^ 4 * 2 ^ a from by ring]
  have : x / 2 ^ 4 * (2 ^ 4 * 2 ^ a) = x / 2 ^ 4 * 2 ^ 4 * 2 ^ a := by ring
  rw [this, ← Nat.add_mul]
  grind

/-- Bridge from 5 BitList limb equivalences to the Nat-level equality. -/
private theorem scalar52_eq_of_bitList_limbs (a : Scalar52) (b : Aeneas.Std.Array U8 32#usize)
    (h : ∀ i < 5, (a : List U64)[i]!.val < 2 ^ 52) (h' : (a : List U64)[4]!.val < 2 ^ 48)
    (hlimb0 : (ofU64 (a : List U64)[0]!).take 52 ≈ₗ ofU8 b[0]! ++ ofU8 b[1]! ++ ofU8 b[2]! ++
        ofU8 b[3]! ++ ofU8 b[4]! ++ ofU8 b[5]! ++ (ofU8 b[6]!).take 4)
    (hlimb1 : (ofU64 (a : List U64)[1]!).take 52 ≈ₗ (ofU8 b[6]!).drop 4 ++
        ofU8 b[7]! ++ ofU8 b[8]! ++ ofU8 b[9]! ++ ofU8 b[10]! ++ ofU8 b[11]! ++ ofU8 b[12]!)
    (hlimb2 : (ofU64 (a : List U64)[2]!).take 52 ≈ₗ ofU8 b[13]! ++ ofU8 b[14]! ++ ofU8 b[15]! ++
        ofU8 b[16]! ++ ofU8 b[17]! ++ ofU8 b[18]! ++ (ofU8 b[19]!).take 4)
    (hlimb3 : (ofU64 (a : List U64)[3]!).take 52 ≈ₗ (ofU8 b[19]!).drop 4 ++
        ofU8 b[20]! ++ ofU8 b[21]! ++ ofU8 b[22]! ++ ofU8 b[23]! ++ ofU8 b[24]! ++ ofU8 b[25]!)
    (hlimb4 : (ofU64 (a : List U64)[4]!).take 48 ≈ₗ ofU8 b[26]! ++ ofU8 b[27]! ++ ofU8 b[28]! ++
        ofU8 b[29]! ++ ofU8 b[30]! ++ ofU8 b[31]!) :
    U8x32_as_Nat b = Scalar52_as_Nat a := by
  -- Convert each BitList equivalence to a Nat identity
  have h0 := hlimb0.toNat_eq
  have h1 := hlimb1.toNat_eq
  have h2 := hlimb2.toNat_eq
  have h3 := hlimb3.toNat_eq
  have h4 := hlimb4.toNat_eq
  -- Phase 1: Expand toNat of bit list operations
  simp only [toNat_take, toNat_drop, toNat_append, toNat_ofU8, toNat_ofU64, ofU8_length,
    length_drop, length_append, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd] at h0 h1 h2 h3 h4
  -- Expand both Nat sums
  unfold U8x32_as_Nat Scalar52_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.reducePow, Nat.reduceMul, one_mul]
  -- Provide limb bounds for omega and recombine shared bytes
  have hb0 := h 0 (by omega)
  have hb1 := h 1 (by omega)
  have hb2 := h 2 (by omega)
  have hb3 := h 3 (by omega)
  have hb6 := shared_byte_recombine b[6]!.val 48
  have hb19 := shared_byte_recombine b[19]!.val 152
  -- Normalize all getElem! to getElem so self[i]! (from Scalar52_as_Nat) and
  -- self[i] (from hlimb hypotheses) become the same term.
  -- Aeneas disables List.getElem!_eq_getElem?_getD, so we must apply it explicitly.
  -- We provide explicit length facts so simp can discharge getElem? side conditions.
  have hls : a.val.length = 5 := a.property
  have hlr : b.val.length = 32 := b.property
  simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem, Option.getD_some, hls, hlr, Nat.reduceLT] at *
  grind

/-- If the 32 bytes are as defined in the function (in the language of `BitList`), then
`U8x32_as_Nat result = Scalar52_as_Nat self` as required. -/
theorem scalar52_eq_of_bitList_bytes
    (self : Scalar52) (result : Aeneas.Std.Array U8 32#usize)
    (h : ∀ i < 5, (self : List U64)[i]!.val < 2 ^ 52) (h' : Scalar52_as_Nat self < L)
    (hb0 : ofU8 result[0]! = (ofU64 (self : List U64)[0]!).extract 0 8)
    (hb1 : ofU8 result[1]! = (ofU64 (self : List U64)[0]!).extract 8 16)
    (hb2 : ofU8 result[2]! = (ofU64 (self : List U64)[0]!).extract 16 24)
    (hb3 : ofU8 result[3]! = (ofU64 (self : List U64)[0]!).extract 24 32)
    (hb4 : ofU8 result[4]! = (ofU64 (self : List U64)[0]!).extract 32 40)
    (hb5 : ofU8 result[5]! = (ofU64 (self : List U64)[0]!).extract 40 48)
    (hb6 : ofU8 result[6]! = (ofU64 (self : List U64)[0]!).extract 48 52 ++
                             (ofU64 (self : List U64)[1]!).extract 0 4)
    (hb7 : ofU8 result[7]! = (ofU64 (self : List U64)[1]!).extract 4 12)
    (hb8 : ofU8 result[8]! = (ofU64 (self : List U64)[1]!).extract 12 20)
    (hb9 : ofU8 result[9]! = (ofU64 (self : List U64)[1]!).extract 20 28)
    (hb10 : ofU8 result[10]! = (ofU64 (self : List U64)[1]!).extract 28 36)
    (hb11 : ofU8 result[11]! = (ofU64 (self : List U64)[1]!).extract 36 44)
    (hb12 : ofU8 result[12]! = (ofU64 (self : List U64)[1]!).extract 44 52)
    (hb13 : ofU8 result[13]! = (ofU64 (self : List U64)[2]!).extract 0 8)
    (hb14 : ofU8 result[14]! = (ofU64 (self : List U64)[2]!).extract 8 16)
    (hb15 : ofU8 result[15]! = (ofU64 (self : List U64)[2]!).extract 16 24)
    (hb16 : ofU8 result[16]! = (ofU64 (self : List U64)[2]!).extract 24 32)
    (hb17 : ofU8 result[17]! = (ofU64 (self : List U64)[2]!).extract 32 40)
    (hb18 : ofU8 result[18]! = (ofU64 (self : List U64)[2]!).extract 40 48)
    (hb19 : ofU8 result[19]! = (ofU64 (self : List U64)[2]!).extract 48 52 ++
                               (ofU64 (self : List U64)[3]!).extract 0 4)
    (hb20 : ofU8 result[20]! = (ofU64 (self : List U64)[3]!).extract 4 12)
    (hb21 : ofU8 result[21]! = (ofU64 (self : List U64)[3]!).extract 12 20)
    (hb22 : ofU8 result[22]! = (ofU64 (self : List U64)[3]!).extract 20 28)
    (hb23 : ofU8 result[23]! = (ofU64 (self : List U64)[3]!).extract 28 36)
    (hb24 : ofU8 result[24]! = (ofU64 (self : List U64)[3]!).extract 36 44)
    (hb25 : ofU8 result[25]! = (ofU64 (self : List U64)[3]!).extract 44 52)
    (hb26 : ofU8 result[26]! = (ofU64 (self : List U64)[4]!).extract 0 8)
    (hb27 : ofU8 result[27]! = (ofU64 (self : List U64)[4]!).extract 8 16)
    (hb28 : ofU8 result[28]! = (ofU64 (self : List U64)[4]!).extract 16 24)
    (hb29 : ofU8 result[29]! = (ofU64 (self : List U64)[4]!).extract 24 32)
    (hb30 : ofU8 result[30]! = (ofU64 (self : List U64)[4]!).extract 32 40)
    (hb31 : ofU8 result[31]! = (ofU64 (self : List U64)[4]!).extract 40 48) :
    U8x32_as_Nat result = Scalar52_as_Nat self := by
  apply scalar52_eq_of_bitList_limbs self result h
    (by have := h 4 (by omega); have := Scalar52_top_limb_lt_of_canonical self h'; grind)
  · -- hlimb0
    rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6]
    rw [List.extract_append_extract _ 0 8 16 (by omega) (by omega),
        List.extract_append_extract _ 0 16 24 (by omega) (by omega),
        List.extract_append_extract _ 0 24 32 (by omega) (by omega),
        List.extract_append_extract _ 0 32 40 (by omega) (by omega),
        List.extract_append_extract _ 0 40 48 (by omega) (by omega)]
    rw [List.take_left' (by simp [List.extract_eq_drop_take, ofU64_length])]
    rw [List.extract_append_extract _ 0 48 52 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]
  · -- hlimb1
    rw [hb6, List.drop_left' (by simp [List.extract_eq_drop_take, ofU64_length])]
    rw [hb7, hb8, hb9, hb10, hb11, hb12]
    rw [List.extract_append_extract _ 0 4 12 (by omega) (by omega),
        List.extract_append_extract _ 0 12 20 (by omega) (by omega),
        List.extract_append_extract _ 0 20 28 (by omega) (by omega),
        List.extract_append_extract _ 0 28 36 (by omega) (by omega),
        List.extract_append_extract _ 0 36 44 (by omega) (by omega),
        List.extract_append_extract _ 0 44 52 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]
  · -- hlimb2
    rw [hb13, hb14, hb15, hb16, hb17, hb18, hb19]
    rw [List.extract_append_extract _ 0 8 16 (by omega) (by omega),
        List.extract_append_extract _ 0 16 24 (by omega) (by omega),
        List.extract_append_extract _ 0 24 32 (by omega) (by omega),
        List.extract_append_extract _ 0 32 40 (by omega) (by omega),
        List.extract_append_extract _ 0 40 48 (by omega) (by omega)]
    rw [List.take_left' (by simp [List.extract_eq_drop_take, ofU64_length])]
    rw [List.extract_append_extract _ 0 48 52 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]
  · -- hlimb3
    rw [hb19, List.drop_left' (by simp [List.extract_eq_drop_take, ofU64_length])]
    rw [hb20, hb21, hb22, hb23, hb24, hb25]
    rw [List.extract_append_extract _ 0 4 12 (by omega) (by omega),
        List.extract_append_extract _ 0 12 20 (by omega) (by omega),
        List.extract_append_extract _ 0 20 28 (by omega) (by omega),
        List.extract_append_extract _ 0 28 36 (by omega) (by omega),
        List.extract_append_extract _ 0 36 44 (by omega) (by omega),
        List.extract_append_extract _ 0 44 52 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]
  · -- hlimb4
    rw [hb26, hb27, hb28, hb29, hb30, hb31]
    rw [List.extract_append_extract _ 0 8 16 (by omega) (by omega),
        List.extract_append_extract _ 0 16 24 (by omega) (by omega),
        List.extract_append_extract _ 0 24 32 (by omega) (by omega),
        List.extract_append_extract _ 0 32 40 (by omega) (by omega),
        List.extract_append_extract _ 0 40 48 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]

-- Remove @[progress] from the Nat-level shift specs and add to the BitList specs.
attribute [-progress] U64.ShiftRight_IScalar_spec
attribute [-progress] U64.ShiftLeft_IScalar_spec
attribute [progress] U64.ShiftRight_IScalar_bitList_spec
attribute [progress] U64.ShiftLeft_IScalar_bitList_spec

set_option maxHeartbeats 1600000 in -- heavy progress and simps
/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`**:
- The result byte array represents the same number as the input unpacked scalar modulo L
- The result is in canonical form (less than L) -/
@[progress]
theorem to_bytes_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧ U8x32_as_Nat result < L ⦄ := by
    unfold to_bytes
    progress*
    -- Simple bytes (30 of 32): each byte = 8-bit extract of its limb
    have ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16,
        hb17, hb18, hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31⟩ :
        ofU8 result[0]! = (ofU64 (self : List U64)[0]!).extract 0 8 ∧
        ofU8 result[1]! = (ofU64 (self : List U64)[0]!).extract 8 16 ∧
        ofU8 result[2]! = (ofU64 (self : List U64)[0]!).extract 16 24 ∧
        ofU8 result[3]! = (ofU64 (self : List U64)[0]!).extract 24 32 ∧
        ofU8 result[4]! = (ofU64 (self : List U64)[0]!).extract 32 40 ∧
        ofU8 result[5]! = (ofU64 (self : List U64)[0]!).extract 40 48 ∧
        ofU8 result[7]! = (ofU64 (self : List U64)[1]!).extract 4 12 ∧
        ofU8 result[8]! = (ofU64 (self : List U64)[1]!).extract 12 20 ∧
        ofU8 result[9]! = (ofU64 (self : List U64)[1]!).extract 20 28 ∧
        ofU8 result[10]! = (ofU64 (self : List U64)[1]!).extract 28 36 ∧
        ofU8 result[11]! = (ofU64 (self : List U64)[1]!).extract 36 44 ∧
        ofU8 result[12]! = (ofU64 (self : List U64)[1]!).extract 44 52 ∧
        ofU8 result[13]! = (ofU64 (self : List U64)[2]!).extract 0 8 ∧
        ofU8 result[14]! = (ofU64 (self : List U64)[2]!).extract 8 16 ∧
        ofU8 result[15]! = (ofU64 (self : List U64)[2]!).extract 16 24 ∧
        ofU8 result[16]! = (ofU64 (self : List U64)[2]!).extract 24 32 ∧
        ofU8 result[17]! = (ofU64 (self : List U64)[2]!).extract 32 40 ∧
        ofU8 result[18]! = (ofU64 (self : List U64)[2]!).extract 40 48 ∧
        ofU8 result[20]! = (ofU64 (self : List U64)[3]!).extract 4 12 ∧
        ofU8 result[21]! = (ofU64 (self : List U64)[3]!).extract 12 20 ∧
        ofU8 result[22]! = (ofU64 (self : List U64)[3]!).extract 20 28 ∧
        ofU8 result[23]! = (ofU64 (self : List U64)[3]!).extract 28 36 ∧
        ofU8 result[24]! = (ofU64 (self : List U64)[3]!).extract 36 44 ∧
        ofU8 result[25]! = (ofU64 (self : List U64)[3]!).extract 44 52 ∧
        ofU8 result[26]! = (ofU64 (self : List U64)[4]!).extract 0 8 ∧
        ofU8 result[27]! = (ofU64 (self : List U64)[4]!).extract 8 16 ∧
        ofU8 result[28]! = (ofU64 (self : List U64)[4]!).extract 16 24 ∧
        ofU8 result[29]! = (ofU64 (self : List U64)[4]!).extract 24 32 ∧
        ofU8 result[30]! = (ofU64 (self : List U64)[4]!).extract 32 40 ∧
        ofU8 result[31]! = (ofU64 (self : List U64)[4]!).extract 40 48 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
        subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
        rw [ofU8_cast_eq_ofU64_take]; simp [ofU64_length, *] }
    -- Shared bytes (2 of 32): OR of adjacent limb nibbles
    have ⟨hb6, hb19⟩ : ofU8 result[6]! = (ofU64 (self : List U64)[0]!).extract 48 52 ++
        (ofU64 (self : List U64)[1]!).extract 0 4 ∧
        ofU8 result[19]! = (ofU64 (self : List U64)[2]!).extract 48 52 ++
        (ofU64 (self : List U64)[3]!).extract 0 4:= by
      have h_or := ofU64_of_or_bv i15 i13 i16 4 (by omega)
        (val_mod_of_replicate_prefix i15 4 _ i15_post)
        (val_lt_of_shift_right i13 i 48 4 i13_post (by
          have := h 0 (by omega); rw [i_post]
          simp only [Array.getElem!_Nat_eq] at this; exact this))
        i16_post2
      have h_or' := ofU64_of_or_bv i45 i43 i46 4 (by omega)
        (val_mod_of_replicate_prefix i45 4 _ i45_post)
        (val_lt_of_shift_right i43 i30 48 4 i43_post (by
          have := h 2 (by omega); rw [i30_post]
          simp only [Array.getElem!_Nat_eq] at this; exact this))
        i46_post2
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      constructor
      · rw [ofU8_cast_eq_ofU64_take, h_or, List.take_append (i := 8)]
        simp [length_take, length_drop, ofU64_length, i13_post, i15_post,
          List.take_take, List.take_append_of_le_length]
      · rw [ofU8_cast_eq_ofU64_take, h_or', List.take_append (i := 8)]
        simp [length_take, length_drop, ofU64_length, i43_post, i45_post,
          List.take_take, List.take_append_of_le_length]
    -- byte-level facts → limb-level facts → Nat equality
    have h_list : ∀ i < 5, (self : List U64)[i]!.val < 2 ^ 52 := by
      intro i hi; have := h i hi
      simp only [Array.getElem!_Nat_eq] at this; exact this
    have := scalar52_eq_of_bitList_bytes self result h_list h'
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15 hb16 hb17 hb18 hb19 hb20
      hb21 hb22 hb23 hb24 hb25 hb26 hb27 hb28 hb29 hb30 hb31
    exact ⟨this, this ▸ h'⟩

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
