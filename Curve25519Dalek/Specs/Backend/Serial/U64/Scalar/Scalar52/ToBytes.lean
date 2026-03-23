/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.BitList
import Curve25519Dalek.ExternallyVerified
#setup_aeneas_simps

/-! # Spec Theorem for `Scalar52::to_bytes`

Specification and proof for `Scalar52::to_bytes`.

This function converts the structure to its byte representation.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

## Rust Source

```rust
/// Pack the limbs of this `Scalar52` into 32 bytes
pub fn to_bytes(self) -> [u8; 32] {
    let mut s = [0u8; 32];

    s[ 0] =  (self.0[ 0] >>  0)                      as u8;
    s[ 1] =  (self.0[ 0] >>  8)                      as u8;
    s[ 2] =  (self.0[ 0] >> 16)                      as u8;
    s[ 3] =  (self.0[ 0] >> 24)                      as u8;
    s[ 4] =  (self.0[ 0] >> 32)                      as u8;
    s[ 5] =  (self.0[ 0] >> 40)                      as u8;
    s[ 6] = ((self.0[ 0] >> 48) | (self.0[ 1] << 4)) as u8;
    s[ 7] =  (self.0[ 1] >>  4)                      as u8;
    s[ 8] =  (self.0[ 1] >> 12)                      as u8;
    s[ 9] =  (self.0[ 1] >> 20)                      as u8;
    s[10] =  (self.0[ 1] >> 28)                      as u8;
    s[11] =  (self.0[ 1] >> 36)                      as u8;
    s[12] =  (self.0[ 1] >> 44)                      as u8;
    s[13] =  (self.0[ 2] >>  0)                      as u8;
    s[14] =  (self.0[ 2] >>  8)                      as u8;
    s[15] =  (self.0[ 2] >> 16)                      as u8;
    s[16] =  (self.0[ 2] >> 24)                      as u8;
    s[17] =  (self.0[ 2] >> 32)                      as u8;
    s[18] =  (self.0[ 2] >> 40)                      as u8;
    s[19] = ((self.0[ 2] >> 48) | (self.0[ 3] << 4)) as u8;
    s[20] =  (self.0[ 3] >>  4)                      as u8;
    s[21] =  (self.0[ 3] >> 12)                      as u8;
    s[22] =  (self.0[ 3] >> 20)                      as u8;
    s[23] =  (self.0[ 3] >> 28)                      as u8;
    s[24] =  (self.0[ 3] >> 36)                      as u8;
    s[25] =  (self.0[ 3] >> 44)                      as u8;
    s[26] =  (self.0[ 4] >>  0)                      as u8;
    s[27] =  (self.0[ 4] >>  8)                      as u8;
    s[28] =  (self.0[ 4] >> 16)                      as u8;
    s[29] =  (self.0[ 4] >> 24)                      as u8;
    s[30] =  (self.0[ 4] >> 32)                      as u8;
    s[31] =  (self.0[ 4] >> 40)                      as u8;

    s
}
```

## Bit layout

Each limb holds 52 bits. Since 52 = 6×8 + 4, each limb fills 6 full bytes plus 4 bits that
spill into a shared byte with the adjacent limb. The two shared bytes are s[6] and s[19],
constructed via OR of the overflow bits from one limb and the start bits of the next.

  | Limb | Bits  | Bytes                              | Shared |
  |------|-------|------------------------------------|--------|
  |  0   | 0–51  | s[0]–s[5], lower nibble of s[6]    | s[6]   |
  |  1   | 0–51  | upper nibble of s[6], s[7]–s[12]   | s[6]   |
  |  2   | 0–51  | s[13]–s[18], lower nibble of s[19] | s[19]  |
  |  3   | 0–51  | upper nibble of s[19], s[20]–s[25] | s[19]  |
  |  4   | 0–47  | s[26]–s[31] (48 bits)              | none   |

Limb 4 uses only 48 of its 52 bits because the precondition `Scalar52_as_Nat self < L < 2^253`
implies `self[4] < 2^(253−208) = 2^45 < 2^48`.

Total: limbs hold 5×52 = 260 bits, but the value fits in 32×8 = 256 bits.

## Proof overview

We prove 5 results, one for each limb, describing the rows of the above table in terms of `BitList`.


-/

set_option linter.style.setOption false
set_option maxHeartbeats 2000000

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52
open List BitList
attribute [local simp] Array.length_eq

/-! ## BitList spec theorems for scalar operations

These theorems express the four key operations (shift right, cast U64→U8, shift left, bitwise OR)
in terms of `BitList` operations (`drop`, `take`, `replicate`, `zipWith`).

They mirror the Nat-level spec theorems from Aeneas but with BitList postconditions:
- Right shift by k ↔ `drop k` (plus zero padding at top)
- Cast U64→U8 ↔ `take 8`
- Left shift by k ↔ `replicate k false ++` (plus truncation)
- Bitwise OR ↔ `zipWith (· || ·)`
-/


private lemma testBit_add_mul_pow_low (b q k i : Nat) (hb : b < 2^k) (hi : i < k) :
    (b + 2^k * q).testBit i = b.testBit i := by
  have h1 : (b + 2^k * q) % 2^k = b := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have h2 := Nat.testBit_mod_two_pow (b + 2^k * q) k i
  rw [h1] at h2; simp [hi] at h2; exact h2.symm

private lemma testBit_add_mul_pow_high (b q k i : Nat) (hb : b < 2^k) (hi : k ≤ i) :
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

/-- Right-shifting a U64 by k drops the bottom k bits (LSB-first).
    The result is `(ofU64 x).drop k` padded with k zeros at the top. -/
theorem U64.ShiftRight_IScalar_bitList_spec {ty1} (x : U64) (y : IScalar ty1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val < 64) :
    (x >>> y) ⦃ z => ofU64 z = (ofU64 x).drop y.toNat ++ List.replicate y.toNat false ⦄ := by
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

/-- Casting a U64 to U8 takes the bottom 8 bits.
    After `subst_vars` inlines cast equalities, `simp [ofU8_cast_eq_ofU64_take]` converts
    all `ofU8 (UScalar.cast .U8 x)` occurrences to `(ofU64 x).take 8`. -/
@[simp]
theorem ofU8_cast_eq_ofU64_take (x : U64) :
    ofU8 (UScalar.cast .U8 x) = (ofU64 x).take 8 := by
  change ofNat 8 (UScalar.cast .U8 x).val = (ofNat 64 x.val).take 8
  rw [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, ofNat_mod,
    ofNat_take 8 64 x.val (by omega)]

/-- Left-shifting a U64 by k prepends k zero bits at the bottom (LSB-first)
    and truncates to 64 bits. -/
theorem U64.ShiftLeft_IScalar_bitList_spec {ty1} (x : U64) (y : IScalar ty1)
    (hy0 : 0 ≤ y.val) (hy1 : y.val < 64) :
    (x <<< y) ⦃ z => ofU64 z = List.replicate y.toNat false ++
      (ofU64 x).take (64 - y.toNat) ⦄ := by
  have hk : y.toNat < 64 := by scalar_tac
  have h := U64.ShiftLeft_IScalar_spec x y hy0 hy1
  exact WP.spec_mono h fun z ⟨hval, _⟩ => by
    change ofNat 64 z.val =
      List.replicate y.toNat false ++ (ofNat 64 x.val).take (64 - y.toNat)
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

/-- Bitwise OR on non-overlapping values: if `x` has zeros in the bottom `k` bits
    and `y` fits in `k` bits, then OR concatenates the respective bit slices.
    This is the pattern used for shared bytes s[6] and s[19], where
    `x = self[j+1] << 4` (zeros in bits 0–3) and `y = self[j] >> 48` (fits in 16 bits). -/
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

-- Note: this is a strengthening of `Scalar52_top_limb_lt_of_as_Nat_lt` in Aux.lean (which gives
-- < 2^51 from < 2^259). This tighter bound should be moved to the central location.
/-- If `Scalar52_as_Nat a < L`, then the top limb `a[4]` is bounded by `2^45`.
This follows because `2^208 * a[4] ≤ Scalar52_as_Nat a < L < 2^253`. -/
theorem Scalar52_top_limb_lt_of_canonical (a : Array U64 5#usize) (h : Scalar52_as_Nat a < L) :
  a[4].val < 2 ^ 45 := by
  unfold Scalar52_as_Nat at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  have : L < 2 ^ 253 := by unfold L; omega
  grind

/-- Two bit lists of the same length with the same `toNat` value are equal. -/
theorem eq_of_toNat_eq_of_length_eq (bs₁ bs₂ : List Bool)
    (h : toNat bs₁ = toNat bs₂) (hl : bs₁.length = bs₂.length) : bs₁ = bs₂ := by
  conv_lhs => rw [← ofNat_toNat bs₁]
  conv_rhs => rw [← ofNat_toNat bs₂]
  rw [hl, h]

/-- Two bit lists of the same length with the same `toNat` value are Equiv. -/
theorem Equiv.of_toNat_eq_of_length_eq (bs₁ bs₂ : List Bool)
    (h : toNat bs₁ = toNat bs₂) (hl : bs₁.length = bs₂.length) : bs₁ ≈ₗ bs₂ := by
  rw [eq_of_toNat_eq_of_length_eq bs₁ bs₂ h hl]

/-- At a shared byte (s[6] or s[19]), the lower and upper nibble contributions recombine:
    `(x % 2^4) * 2^a + (x / 2^4) * 2^(a+4) = x * 2^a`. -/
theorem shared_byte_recombine (x a : Nat) :
    (x % 2 ^ 4) * 2 ^ a + (x / 2 ^ 4) * 2 ^ (a + 4) = x * 2 ^ a := by
  conv_lhs => rw [show (2 : Nat) ^ (a + 4) = 2 ^ 4 * 2 ^ a from by ring]
  have : x / 2 ^ 4 * (2 ^ 4 * 2 ^ a) = x / 2 ^ 4 * 2 ^ 4 * 2 ^ a := by ring
  rw [this, ← Nat.add_mul]
  congr 1; omega

/-- Casting a right-shifted U64 to U8 gives the corresponding 8-bit slice as a BitList.
    Given `z.val = x.val / 2^k % 2^8` (which holds after shift-right by k then cast to U8),
    we get `ofU8 z = ((ofU64 x).drop k).take 8`. -/
theorem ofU8_val_eq_ofU64_drop_take (z : U8) (x : U64) (k : Nat)
    (hk : k + 8 ≤ 64) (hval : z.val = x.val / 2 ^ k % 2 ^ 8) :
    ofU8 z = ((ofU64 x).drop k).take 8 := by
  change ofNat 8 z.val = ((ofNat 64 x.val).drop k).take 8
  rw [hval, ofNat_mod, ofNat_drop k 64 x.val (by omega), ofNat_take 8 (64 - k) _ (by omega)]

/-- Bridge from 5 BitList limb equivalences to the Nat-level equality
    `U8x32_as_Nat result = Scalar52_as_Nat self`. -/
theorem scalar52_eq_of_bitList_limbs
    (self : Scalar52) (result : Aeneas.Std.Array U8 32#usize)
    (h : ∀ i : Fin 5, self[i].val < 2 ^ 52)
    (h4_bound : self[4].val < 2 ^ 48)
    (hlimb0 : (ofU64 self[0]).take 52 ≈ₗ
        ofU8 result[0]! ++ ofU8 result[1]! ++ ofU8 result[2]! ++
        ofU8 result[3]! ++ ofU8 result[4]! ++ ofU8 result[5]! ++
        (ofU8 result[6]!).take 4)
    (hlimb1 : (ofU64 self[1]).take 52 ≈ₗ
        (ofU8 result[6]!).drop 4 ++
        ofU8 result[7]! ++ ofU8 result[8]! ++ ofU8 result[9]! ++
        ofU8 result[10]! ++ ofU8 result[11]! ++ ofU8 result[12]!)
    (hlimb2 : (ofU64 self[2]).take 52 ≈ₗ
        ofU8 result[13]! ++ ofU8 result[14]! ++ ofU8 result[15]! ++
        ofU8 result[16]! ++ ofU8 result[17]! ++ ofU8 result[18]! ++
        (ofU8 result[19]!).take 4)
    (hlimb3 : (ofU64 self[3]).take 52 ≈ₗ
        (ofU8 result[19]!).drop 4 ++
        ofU8 result[20]! ++ ofU8 result[21]! ++ ofU8 result[22]! ++
        ofU8 result[23]! ++ ofU8 result[24]! ++ ofU8 result[25]!)
    (hlimb4 : (ofU64 self[4]).take 48 ≈ₗ
        ofU8 result[26]! ++ ofU8 result[27]! ++ ofU8 result[28]! ++
        ofU8 result[29]! ++ ofU8 result[30]! ++ ofU8 result[31]!) :
    U8x32_as_Nat result = Scalar52_as_Nat self := by
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
  have hb0 : self[0].val < 2 ^ 52 := h ⟨0, by omega⟩
  have hb1 : self[1].val < 2 ^ 52 := h ⟨1, by omega⟩
  have hb2 : self[2].val < 2 ^ 52 := h ⟨2, by omega⟩
  have hb3 : self[3].val < 2 ^ 52 := h ⟨3, by omega⟩
  have hb6 := shared_byte_recombine result[6]!.val 48
  have hb19 := shared_byte_recombine result[19]!.val 152
  -- Normalize all getElem! to getElem so self[i]! (from Scalar52_as_Nat) and
  -- self[i] (from hlimb hypotheses) become the same term.
  -- Aeneas disables List.getElem!_eq_getElem?_getD, so we must apply it explicitly.
  -- We provide explicit length facts so simp can discharge getElem? side conditions.
  have hls : self.val.length = 5 := self.property
  have hlr : result.val.length = 32 := result.property
  simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem, Option.getD_some, hls, hlr, Nat.reduceLT] at *
  grind


-- Remove @[progress] from the old Nat-level shift specs and add to the new BitList specs.
-- The cast (progress_pure_def) and OR (lift) keep their original progress behavior;
-- use ofU8_cast_eq_ofU64_take and ofU64_or_non_overlapping manually after progress.
attribute [-progress] U64.ShiftRight_IScalar_spec
attribute [-progress] U64.ShiftLeft_IScalar_spec
attribute [progress] U64.ShiftRight_IScalar_bitList_spec
attribute [progress] U64.ShiftLeft_IScalar_bitList_spec

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
    -- subst_vars
    -- simp only [ofU8_cast_eq_ofU64_take] at *

    -- Limb-level BitList equivalences (one per row of the bit layout table)

    -- Limb 0: s[0]–s[5] and lower nibble of s[6]
    have hlimb0 : (ofU64 self[0]).take 52 ≈ₗ
        ofU8 result[0]! ++ ofU8 result[1]! ++ ofU8 result[2]! ++
        ofU8 result[3]! ++ ofU8 result[4]! ++ ofU8 result[5]! ++
        (ofU8 result[6]!).take 4 := by
      subst_vars
      simp

      sorry

    -- Limb 1: upper nibble of s[6] and s[7]–s[12]
    have hlimb1 : (ofU64 self[1]).take 52 ≈ₗ
        (ofU8 result[6]!).drop 4 ++
        ofU8 result[7]! ++ ofU8 result[8]! ++ ofU8 result[9]! ++
        ofU8 result[10]! ++ ofU8 result[11]! ++ ofU8 result[12]! := by
      sorry

    -- Limb 2: s[13]–s[18] and lower nibble of s[19]
    have hlimb2 : (ofU64 self[2]).take 52 ≈ₗ
        ofU8 result[13]! ++ ofU8 result[14]! ++ ofU8 result[15]! ++
        ofU8 result[16]! ++ ofU8 result[17]! ++ ofU8 result[18]! ++
        (ofU8 result[19]!).take 4 := by
      sorry

    -- Limb 3: upper nibble of s[19] and s[20]–s[25]
    have hlimb3 : (ofU64 self[3]).take 52 ≈ₗ
        (ofU8 result[19]!).drop 4 ++
        ofU8 result[20]! ++ ofU8 result[21]! ++ ofU8 result[22]! ++
        ofU8 result[23]! ++ ofU8 result[24]! ++ ofU8 result[25]! := by
      sorry

    -- Limb 4: s[26]–s[31] (48 bits, no shared byte)
    have hlimb4 : (ofU64 self[4]).take 48 ≈ₗ
        ofU8 result[26]! ++ ofU8 result[27]! ++ ofU8 result[28]! ++
        ofU8 result[29]! ++ ofU8 result[30]! ++ ofU8 result[31]! := by
      sorry

    -- Bridge: combine limb equivalences into the Nat-level equality
    have hlimb_bounds : ∀ i : Fin 5, self[i].val < 2 ^ 52 := by
      intro ⟨i, hi⟩
      simpa [hi] using h i hi
    have : U8x32_as_Nat result = Scalar52_as_Nat self :=
      scalar52_eq_of_bitList_limbs self result hlimb_bounds
        (by have := Scalar52_top_limb_lt_of_canonical self h'; omega)
        hlimb0 hlimb1 hlimb2 hlimb3 hlimb4
    refine ⟨this, ?_⟩
    rw [this]
    exact h'

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
