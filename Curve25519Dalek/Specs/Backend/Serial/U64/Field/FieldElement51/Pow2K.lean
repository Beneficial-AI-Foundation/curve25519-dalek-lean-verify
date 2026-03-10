/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

set_option linter.hashCommand false
#setup_aeneas_simps

/- # Spec Theorem for `FieldElement51::pow2k`

Specification and proof for `FieldElement51::pow2k`.

This function computes the 2^k-th power of the element.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

## Source code

```rust
    /// Given `k > 0`, return `self^(2^k)`.
    #[rustfmt::skip] // keep alignment of c* calculations
    pub fn pow2k(&self, mut k: u32) -> FieldElement51 {

        debug_assert!( k > 0 );

        /// Multiply two 64-bit integers with 128 bits of output.
        #[inline(always)]
        fn m(x: u64, y: u64) -> u128 {
            (x as u128) * (y as u128)
        }

        let mut a: [u64; 5] = self.0;

        while k > 0 {
            // Precondition: assume input limbs a[i] are bounded as
            //
            // a[i] < 2^(51 + b)
            //
            // where b is a real parameter measuring the "bit excess" of the limbs.

            // Precomputation: 64-bit multiply by 19.
            //
            // This fits into a u64 whenever 51 + b + lg(19) < 64.
            //
            // Since 51 + b + lg(19) < 51 + 4.25 + b
            //                       = 55.25 + b,
            // this fits if b < 8.75.
            let a3_19 = 19 * a[3];
            let a4_19 = 19 * a[4];

            // Multiply to get 128-bit coefficients of output.
            //
            // The 128-bit multiplications by 2 turn into 1 slr + 1 slrd each,
            // which doesn't seem any better or worse than doing them as precomputations
            // on the 64-bit inputs.
            let     c0: u128 = m(a[0],  a[0]) + 2*( m(a[1], a4_19) + m(a[2], a3_19) );
            let mut c1: u128 = m(a[3], a3_19) + 2*( m(a[0],  a[1]) + m(a[2], a4_19) );
            let mut c2: u128 = m(a[1],  a[1]) + 2*( m(a[0],  a[2]) + m(a[4], a3_19) );
            let mut c3: u128 = m(a[4], a4_19) + 2*( m(a[0],  a[3]) + m(a[1],  a[2]) );
            let mut c4: u128 = m(a[2],  a[2]) + 2*( m(a[0],  a[4]) + m(a[1],  a[3]) );

            // Same bound as in multiply:
            //    c[i] < 2^(102 + 2*b) * (1+i + (4-i)*19)
            //         < 2^(102 + lg(1 + 4*19) + 2*b)
            //         < 2^(108.27 + 2*b)
            //
            // The carry (c[i] >> 51) fits into a u64 when
            //    108.27 + 2*b - 51 < 64
            //    2*b < 6.73
            //    b < 3.365.
            //
            // So we require b < 3 to ensure this fits.

            const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;

            // Casting to u64 and back tells the compiler that the carry is bounded by 2^64, so
            // that the addition is a u128 + u64 rather than u128 + u128.
            c1 += ((c0 >> 51) as u64) as u128;
            a[0] = (c0 as u64) & LOW_51_BIT_MASK;

            c2 += ((c1 >> 51) as u64) as u128;
            a[1] = (c1 as u64) & LOW_51_BIT_MASK;

            c3 += ((c2 >> 51) as u64) as u128;
            a[2] = (c2 as u64) & LOW_51_BIT_MASK;

            c4 += ((c3 >> 51) as u64) as u128;
            a[3] = (c3 as u64) & LOW_51_BIT_MASK;

            let carry: u64 = (c4 >> 51) as u64;
            a[4] = (c4 as u64) & LOW_51_BIT_MASK;

            // To see that this does not overflow, we need a[0] + carry * 19 < 2^64.
            //
            // c4 < a2^2 + 2*a0*a4 + 2*a1*a3 + (carry from c3)
            //    < 2^(102 + 2*b + lg(5)) + 2^64.
            //
            // When b < 3 we get
            //
            // c4 < 2^110.33  so that carry < 2^59.33
            //
            // so that
            //
            // a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58
            //
            // and there is no overflow.
            a[0] += carry * 19;

            // Now a[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).
            a[1] += a[0] >> 51;
            a[0] &= LOW_51_BIT_MASK;

            // Now all a[i] < 2^(51 + epsilon) and a = self^(2^k).

            k -= 1;
        }

        FieldElement51(a)
    }
```

## Proof strategy

The proof proceeds in three stages. At each stage we prove the key results required for the next
steps and clear all the other hypothesis. See the comments within the proof for details of the
precise intermediate results.

-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.pow2k

@[progress]
theorem m_spec (x y : U64) :
    m x y ⦃ (result : U128) => result.val = x.val * y.val ⦄ := by
  unfold pow2k.m
  progress*

@[progress]
theorem LOW_51_BIT_MASK_spec :
    LOW_51_BIT_MASK ⦃ (result : U64) => result.val = 2^51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK
  progress*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.pow2k

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-! ### Bounds for carry chain (< 2^115)

These bounds ensure that the carry from each intermediate value fits in U64 without truncation. -/

/-- c0 < 77 * 2^108 < 2^115 -/
lemma c0_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)) < 2 ^ 115 := by
  have : a0 * a0 < 2 ^ 108 := by nlinarith
  have : a1 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (77 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c1 < 59 * 2^108 < 2^115 -/
lemma c1_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4)) < 2 ^ 115 := by
  have : a3 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a1 < 2 ^ 108 := by nlinarith
  have : a2 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : (59 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c2 < 41 * 2^108 < 2^115 -/
lemma c2_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3)) < 2 ^ 115 := by
  have : a1 * a1 < 2 ^ 108 := by nlinarith
  have : a0 * a2 < 2 ^ 108 := by nlinarith
  have : a4 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (41 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c3 < 23 * 2^108 < 2^115 -/
lemma c3_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2) < 2 ^ 115 := by
  have : a4 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a3 < 2 ^ 108 := by nlinarith
  have : a1 * a2 < 2 ^ 108 := by nlinarith
  have : (23 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c4 < 5 * 2^108 < 2^115 -/
lemma c4_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a2 * a2 + 2 * (a0 * a4 + a1 * a3) < 2 ^ 115 := by
  have : a2 * a2 < 2 ^ 108 := by nlinarith
  have : a0 * a4 < 2 ^ 108 := by nlinarith
  have : a1 * a3 < 2 ^ 108 := by nlinarith
  have : (5 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- Generic carry chain bound: if formula < K * 2^108 and carry < 2^64 and K ≤ 127, then sum < 2^115 -/
private lemma carry_chain_lt_pow2_115 (formula carry : ℕ) (K : ℕ)
    (hf : formula < K * 2 ^ 108) (hc : carry < 2 ^ 64) (hK : K ≤ 127) :
    formula + carry < 2 ^ 115 := by
  have : K * 2 ^ 108 + 2 ^ 64 ≤ 128 * 2 ^ 108 := by omega
  have : (128 : ℕ) * 2 ^ 108 = 2 ^ 115 := by decide
  omega

/-- Tight bound: c1 formula < 59 * 2^108 -/
private lemma c1_lt_tight (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4)) < 59 * 2 ^ 108 := by
  have : a3 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a1 < 2 ^ 108 := by nlinarith
  have : a2 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  omega

/-- Tight bound: c2 formula < 41 * 2^108 -/
private lemma c2_lt_tight (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3)) < 41 * 2 ^ 108 := by
  have : a1 * a1 < 2 ^ 108 := by nlinarith
  have : a0 * a2 < 2 ^ 108 := by nlinarith
  have : a4 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  omega

/-- Tight bound: c3 formula < 23 * 2^108 -/
private lemma c3_lt_tight (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2) < 23 * 2 ^ 108 := by
  have : a4 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a3 < 2 ^ 108 := by nlinarith
  have : a1 * a2 < 2 ^ 108 := by nlinarith
  omega

/-- Tight bound: c4 formula < 5 * 2^108 -/
private lemma c4_lt_tight (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a2 * a2 + 2 * (a0 * a4 + a1 * a3) < 5 * 2 ^ 108 := by
  have : a2 * a2 < 2 ^ 108 := by nlinarith
  have : a0 * a4 < 2 ^ 108 := by nlinarith
  have : a1 * a3 < 2 ^ 108 := by nlinarith
  omega

/-- Squaring in radix-2^51, mod p, key algebraic identity underlying field squaring. -/
lemma decompose (a0 a1 a2 a3 a4 : ℕ) :
    (a0 + 2^51 * a1 + 2^102 * a2 + 2^153 * a3 + 2^204 * a4)^2
    ≡ a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)) +
      2^51 * (a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4))) +
      2^102 * (a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3))) +
      2^153 * (a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2)) +
      2^204 * (a2 * a2 + 2 * (a0 * a4 + a1 * a3)) [MOD p] := by
  have expand : (a0 + 2^51 * a1 + 2^102 * a2 + 2^153 * a3 + 2^204 * a4)^2 =
    a0^2 +
    2^51 * (2 * a0 * a1) +
    2^102 * (a1^2 + 2 * a0 * a2) +
    2^153 * (2 * a0 * a3 + 2 * a1 * a2) +
    2^204 * (a2^2 + 2 * a0 * a4 + 2 * a1 * a3) +
    2^255 * ((2 * a1 * a4 + 2 * a2 * a3) +
      2^51 * (a3^2 + 2 * a2 * a4) +
      2^102 * (2 * a3 * a4) +
      2^153 * a4^2) := by ring
  rw [expand]
  have key : (2 : ℕ)^255 ≡ 19 [MOD p] := by unfold p; rw [Nat.ModEq]; norm_num
  have := Nat.ModEq.mul_right ((2 * a1 * a4 + 2 * a2 * a3) +
    2^51 * (a3^2 + 2 * a2 * a4) + 2^102 * (2 * a3 * a4) + 2^153 * a4^2) key
  have := Nat.ModEq.add_left (a0^2 +
    2^51 * (2 * a0 * a1) +
    2^102 * (a1^2 + 2 * a0 * a2) +
    2^153 * (2 * a0 * a3 + 2 * a1 * a2) +
    2^204 * (a2^2 + 2 * a0 * a4 + 2 * a1 * a3)) this
  apply Nat.ModEq.trans this
  have : a0^2 + 2^51 * (2 * a0 * a1) + 2^102 * (a1^2 + 2 * a0 * a2) +
      2^153 * (2 * a0 * a3 + 2 * a1 * a2) + 2^204 * (a2^2 + 2 * a0 * a4 + 2 * a1 * a3) +
      19 * (2 * a1 * a4 + 2 * a2 * a3 + 2^51 * (a3^2 + 2 * a2 * a4) +
        2^102 * (2 * a3 * a4) + 2^153 * a4^2) =
    a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)) +
    2^51 * (a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4))) +
    2^102 * (a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3))) +
    2^153 * (a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2)) +
    2^204 * (a2 * a2 + 2 * (a0 * a4 + a1 * a3)) := by ring
  rw [this]

/-- Carry chain conservation: the radix-2^51 sum is preserved through 5 carry steps. -/
private lemma carry_chain_eq (c0 c1 c2 c3 c4 a0 a1 a2 a3 a4 carry c1' c2' c3' c4' : ℕ)
    (ha0 : a0 = c0 % 2 ^ 51) (ha1 : a1 = c1' % 2 ^ 51) (ha2 : a2 = c2' % 2 ^ 51)
    (ha3 : a3 = c3' % 2 ^ 51) (ha4 : a4 = c4' % 2 ^ 51)
    (hc1' : c1' = c1 + c0 / 2 ^ 51) (hc2' : c2' = c2 + c1' / 2 ^ 51)
    (hc3' : c3' = c3 + c2' / 2 ^ 51) (hc4' : c4' = c4 + c3' / 2 ^ 51)
    (hcarry : carry = c4' / 2 ^ 51) :
    c0 + 2^51*c1 + 2^102*c2 + 2^153*c3 + 2^204*c4 =
    a0 + 2^51*a1 + 2^102*a2 + 2^153*a3 + 2^204*a4 + 2^255*carry := by omega

set_option maxHeartbeats 2000000 in
-- Required for progress*
@[progress]
theorem pow2k_loop_spec (k : U32) (a : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    pow2k_loop k a ⦃ (result : Std.Array U64 5#usize) =>
      Field51_as_Nat result ≡ (Field51_as_Nat a)^(2^k.val) [MOD p] ∧
      (if k.val = 0 then result = a else ∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold pow2k_loop
  split
  case isTrue hlt =>
    -- Progress through the loop body to the 1st halt point, name c0 c1 c2 c3 c4
    iterate 12 progress
    progress as ⟨ c0, _ ⟩
    iterate 5 progress
    progress as ⟨ c1, _ ⟩
    iterate 5 progress
    progress as ⟨ c2, _ ⟩
    iterate 5 progress
    progress as ⟨ c3, _ ⟩
    iterate 5 progress
    progress as ⟨ c4, _ ⟩
    /-
    Stage 1: The 5 intermediate products (c0-c4) have been computed

    Values (`hc0`-`hc4`):
      `c0 = a[0]² + 2·(a[1]·(19·a[4]) + a[2]·(19·a[3]))`
      `c1 = (19·a[3])·a[3] + 2·(a[0]·a[1] + a[2]·(19·a[4]))`
      `c2 = a[1]² + 2·(a[0]·a[2] + a[4]·(19·a[3]))`
      `c3 = (19·a[4])·a[4] + 2·(a[0]·a[3] + a[1]·a[2])`
      `c4 = a[2]² + 2·(a[0]·a[4] + a[1]·a[3])`

    Bounds (`hc0'`-`hc4'`):
      `c0.val < 2^115`, ..., `c4.val < 2^115`

    Algebraic identity (`a_pow_two`):
      `c0 + 2^51·c1 + 2^102·c2 + 2^153·c3 + 2^204·c4 ≡ (Field51_as_Nat a)² [MOD p]`
    -/
    subst_vars
    have hc0 : c0.val = a[0]!.val * a[0]!.val + 2 *
        (a[1]!.val * (19 * a[4]!.val) + a[2]!.val * (19 * a[3]!.val)) := by simp [*]
    have hc1 : c1.val = a[3]!.val *
        (19 * a[3]!.val) + 2 * (a[0]!.val * a[1]!.val + a[2]!.val * (19 * a[4]!.val)) := by simp [*]
    have hc2 : c2.val = a[1]!.val * a[1]!.val + 2 *
        (a[0]!.val * a[2]!.val + a[4]!.val * (19 * a[3]!.val)) := by simp [*]
    have hc3 : c3.val = a[4]!.val * (19 * a[4]!.val) + 2 *
        (a[0]!.val * a[3]!.val + a[1]!.val * a[2]!.val) := by simp [*]
    have hc4 : c4.val = a[2]!.val * a[2]!.val + 2 *
        (a[0]!.val * a[4]!.val + a[1]!.val * a[3]!.val) := by simp [*]
    have hc0' : c0.val < 2 ^ 115 := by simp only [hc0]; apply c0_lt_pow2_115 <;> exact ha _ (by simp)
    have hc1' : c1.val < 2 ^ 115 := by simp only [hc1]; apply c1_lt_pow2_115 <;> exact ha _ (by simp)
    have hc2' : c2.val < 2 ^ 115 := by simp only [hc2]; apply c2_lt_pow2_115 <;> exact ha _ (by simp)
    have hc3' : c3.val < 2 ^ 115 := by simp only [hc3]; apply c3_lt_pow2_115 <;> exact ha _ (by simp)
    have hc4' : c4.val < 2 ^ 115 := by simp only [hc4]; apply c4_lt_pow2_115 <;> exact ha _ (by simp)
    have a_pow_two : (c0.val + 2^51 * c1.val + 2^102 * c2.val + 2^153 * c3.val + 2^204 * c4.val)
        ≡ (Field51_as_Nat a)^2 [MOD p] := by
      have := decompose a[0]!.val a[1]!.val a[2]!.val a[3]!.val a[4]!.val
      simp_all only [Nat.ModEq, Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, mul_zero, pow_zero, one_mul]
    -- Clear Stage 1 intermediates, keeping only what's needed going forward
    clear * - pow2k_loop_spec k a ha hlt
      c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc0' hc1' hc2' hc3' hc4' a_pow_two
    -- Continue to the 2nd halt point
    progress as ⟨ _, i30_post_1, _ ⟩
    progress as ⟨ _, i31_post ⟩
    progress as ⟨ _, i32_post ⟩
    progress as ⟨ c1', c1'_post ⟩
    progress as ⟨ _, i33_post ⟩
    progress as ⟨ _, mask_post ⟩
    progress as ⟨ _, i34_post_1, _ ⟩
    progress as ⟨ _, a1_post ⟩
    progress as ⟨ _, i35_post_1, _ ⟩
    progress as ⟨ _, i36_post ⟩
    progress as ⟨ _, i37_post ⟩
    progress as ⟨ c2', c2'_post ⟩
    progress as ⟨ _, i38_post ⟩
    progress as ⟨ _, i39_post_1, _ ⟩
    progress as ⟨ _, a2_post ⟩
    progress as ⟨ _, i40_post_1, _ ⟩
    progress as ⟨ _, i41_post ⟩
    progress as ⟨ _, i42_post ⟩
    progress as ⟨ c3', c3'_post ⟩
    progress as ⟨ _, i43_post ⟩
    progress as ⟨ _, i44_post_1, _ ⟩
    progress as ⟨ _, a3_post ⟩
    progress as ⟨ _, i45_post_1, _ ⟩
    progress as ⟨ _, i46_post ⟩
    progress as ⟨ _, i47_post ⟩
    progress as ⟨ c4', c4'_post ⟩
    progress as ⟨ _, i48_post ⟩
    progress as ⟨ _, i49_post_1, _ ⟩
    progress as ⟨ _, a4_post ⟩
    progress as ⟨ _, i50_post_1, _ ⟩
    progress as ⟨ carry, carry_post ⟩
    progress as ⟨ _, i51_post ⟩
    progress as ⟨ _, i52_post_1, _ ⟩
    progress as ⟨ a', a'_post ⟩
    /-
    Stage 2: Carry propagation

    The Rust code propagates carries through c1–c4:
    ```rust
      c1 += (c0 >> 51) as u64;  a[0] = (c0 as u64) & LOW_51_BIT_MASK;
      c2 += (c1 >> 51) as u64;  a[1] = (c1 as u64) & LOW_51_BIT_MASK;
      c3 += (c2 >> 51) as u64;  a[2] = (c2 as u64) & LOW_51_BIT_MASK;
      c4 += (c3 >> 51) as u64;  a[3] = (c3 as u64) & LOW_51_BIT_MASK;
      carry = (c4 >> 51) as u64; a[4] = (c4 as u64) & LOW_51_BIT_MASK;
    ```

    We name the carry-propagated accumulators `c1'`,.., `c4'`:
      `c1' = c1 + (c0 >> 51)`      `c2' = c2 + (c1' >> 51)`
      `c3' = c3 + (c2' >> 51)`     `c4' = c4 + (c3' >> 51)`

    Carry-fits bounds (`hcarry0_fits`–`hcarry4_fits`):
      `c0/2^51 < 2^64`, `c1'/2^51 < 2^64`, ..., `c4'/2^51 < 2^64`

    Accumulator bounds (`hc1'_bound`–`hc4'_bound`):
      `c1' < 2^115`, `c2' < 2^115`, `c3' < 2^115`, `c4' < 2^115`

    Array values (`ha'_0`–`ha'_4`):
      `a[0] = c0 % 2^51`       `a[1] = c1' % 2^51`      `a[2] = c2' % 2^51`
      `a[3] = c3' % 2^51`      `a[4] = c4' % 2^51`

    Carry value (`hcarry_val`):
      `carry = c4' / 2^51`
    -/
    -- Interleaved carry chain: each step needs the previous carry-fits bound for omega
    -- to eliminate the % 2^64 from the U128→U64→U128 cast chain.
    have hcarry0_fits : c0.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c0.val hc0'
    -- c1' = c1 + carry from c0
    have hc1'_eq : c1'.val = c1.val + c0.val / 2 ^ 51 := by
      simp only [c1'_post, i32_post, i31_post, i30_post_1, UScalar.cast_val_eq,
        UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
      omega
    have hc1'_bound : c1'.val < 2 ^ 115 := by
      rw [hc1'_eq]; apply carry_chain_lt_pow2_115 _ _ 59 _ hcarry0_fits (by omega)
      rw [hc1]; exact c1_lt_tight _ _ _ _ _
        (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp))
    have hcarry1_fits : c1'.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c1'.val hc1'_bound
    -- c2' = c2 + carry from c1'
    have hc2'_eq : c2'.val = c2.val + c1'.val / 2 ^ 51 := by
      simp only [c2'_post, i37_post, i36_post, i35_post_1, UScalar.cast_val_eq,
        UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
      omega
    have hc2'_bound : c2'.val < 2 ^ 115 := by
      rw [hc2'_eq]; apply carry_chain_lt_pow2_115 _ _ 41 _ hcarry1_fits (by omega)
      rw [hc2]; exact c2_lt_tight _ _ _ _ _
        (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp))
    have hcarry2_fits : c2'.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c2'.val hc2'_bound
    -- c3' = c3 + carry from c2'
    have hc3'_eq : c3'.val = c3.val + c2'.val / 2 ^ 51 := by
      simp only [c3'_post, i42_post, i41_post, i40_post_1, UScalar.cast_val_eq,
        UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
      omega
    have hc3'_bound : c3'.val < 2 ^ 115 := by
      rw [hc3'_eq]; apply carry_chain_lt_pow2_115 _ _ 23 _ hcarry2_fits (by omega)
      rw [hc3]; exact c3_lt_tight _ _ _ _ _
        (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp))
    have hcarry3_fits : c3'.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c3'.val hc3'_bound
    -- c4' = c4 + carry from c3'
    have hc4'_eq : c4'.val = c4.val + c3'.val / 2 ^ 51 := by
      simp only [c4'_post, i47_post, i46_post, i45_post_1, UScalar.cast_val_eq,
        UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
      omega
    have hc4'_bound : c4'.val < 2 ^ 115 := by
      rw [hc4'_eq]; apply carry_chain_lt_pow2_115 _ _ 5 _ hcarry3_fits (by omega)
      rw [hc4]; exact c4_lt_tight _ _ _ _ _
        (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp))
    have hcarry4_fits : c4'.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c4'.val hc4'_bound
    -- Array values after carry propagation
    -- Each ha'_i traces: a'[i]! → chain of set operations → AND with mask → ci % 2^51
    -- Strategy: use set_of_ne_getElem! to peel through non-matching sets, set_of_eq at the match
    have ha'_0 : a'[0]!.val = c0.val % 2 ^ 51 := by
      simp only [a'_post, Array.set_of_ne_getElem! _ _ 0 4 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a4_post, Array.set_of_ne_getElem! _ _ 0 3 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a3_post, Array.set_of_ne_getElem! _ _ 0 2 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a2_post, Array.set_of_ne_getElem! _ _ 0 1 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a1_post, Array.set_of_eq _ _ 0 (by scalar_tac)]
      simp only [i34_post_1, UScalar.val_and, i33_post, UScalar.cast_val_eq, UScalarTy.numBits]
      simp_all only [Nat.and_two_pow_sub_one_eq_mod];
      omega
    have ha'_1 : a'[1]!.val = c1'.val % 2 ^ 51 := by
      simp only [a'_post, Array.set_of_ne_getElem! _ _ 1 4 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a4_post, Array.set_of_ne_getElem! _ _ 1 3 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a3_post, Array.set_of_ne_getElem! _ _ 1 2 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a2_post, Array.set_of_eq _ _ 1 (by scalar_tac)]
      simp only [i39_post_1, UScalar.val_and, i38_post, UScalar.cast_val_eq, UScalarTy.numBits]
      simp_all only [Nat.and_two_pow_sub_one_eq_mod]; omega
    have ha'_2 : a'[2]!.val = c2'.val % 2 ^ 51 := by
      simp only [a'_post, Array.set_of_ne_getElem! _ _ 2 4 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a4_post, Array.set_of_ne_getElem! _ _ 2 3 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a3_post, Array.set_of_eq _ _ 2 (by scalar_tac)]
      simp only [i44_post_1, UScalar.val_and, i43_post, UScalar.cast_val_eq, UScalarTy.numBits]
      simp_all only [Nat.and_two_pow_sub_one_eq_mod]; omega
    have ha'_3 : a'[3]!.val = c3'.val % 2 ^ 51 := by
      simp only [a'_post, Array.set_of_ne_getElem! _ _ 3 4 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a4_post, Array.set_of_eq _ _ 3 (by scalar_tac)]
      simp only [i49_post_1, UScalar.val_and, i48_post, UScalar.cast_val_eq, UScalarTy.numBits]
      simp_all only [Nat.and_two_pow_sub_one_eq_mod]; omega
    have ha'_4 : a'[4]!.val = c4'.val % 2 ^ 51 := by
      simp only [a'_post, Array.set_of_eq _ _ 4 (by scalar_tac)]
      simp only [i52_post_1, UScalar.val_and, i51_post, UScalar.cast_val_eq, UScalarTy.numBits]
      simp_all only [Nat.and_two_pow_sub_one_eq_mod]
      omega
    have hcarry_val : carry.val = c4'.val / 2 ^ 51 := by
      simp only [carry_post, i50_post_1, UScalar.cast_val_eq, UScalarTy.numBits,
        Nat.shiftRight_eq_div_pow]
      omega
    -- Clear Stage 2 postconditions
    clear * - pow2k_loop_spec k a ha hlt c0 c1 c2 c3 c4
      hc0 hc1 hc2 hc3 hc4 hc0' hc1' hc2' hc3' hc4' a_pow_two
      c1' c2' c3' c4' carry a' mask_post
      hcarry0_fits hc1'_eq hc1'_bound hcarry1_fits hc2'_eq hc2'_bound hcarry2_fits
      hc3'_eq hc3'_bound hcarry3_fits hc4'_eq hc4'_bound hcarry4_fits
      ha'_0 ha'_1 ha'_2 ha'_3 ha'_4 hcarry_val
    -- Continue until the end of the function
    progress as ⟨ _, _ ⟩
    progress as ⟨ _, _ ⟩
    progress as ⟨ i55, _ ⟩
    progress as ⟨ a6, a6_post ⟩
    progress as ⟨ i56, _ ⟩
    progress as ⟨ i57, i57_post_1, _ ⟩
    progress as ⟨ i58, _ ⟩
    -- TODO: Progress needs to apply `U64.add_spec` but gets stuck trying to solve the precondition
    apply spec_bind
    · apply U64.add_spec
      have : i58.val < 2 ^ 51 := by
        have : i58.val = a'[1]!.val := by simp [*]
        rw [this, ha'_1]; exact Nat.mod_lt _ (by positivity)
      rw [i57_post_1]
      have : i56.val >>> 51 ≤ 2 ^ 13 - 1 := U64_shiftRight_le i56
      have : U64.max = 2 ^ 64 - 1 := by simp only [U64.max_eq]; norm_num
      omega
    intro i59 i59_post
    progress as ⟨ a7, a7_post ⟩
    progress as ⟨ i60, _ ⟩
    progress as ⟨ _, i61_post_1, _ ⟩
    progress as ⟨ a'', a''_post ⟩
    /-
    Stage 3: Final reduction (Rust l.534–545)

    The Rust code reduces `carry` back into the low limb:
    ```rust
      a[0] += carry * 19;
      a[1] += a[0] >> 51;
      a[0] &= LOW_51_BIT_MASK;
    ```
    Writing `a'` for the array from stage 2 and `a''` for the output, we prove (`ha''_0`–`ha''_4`):
      `a[0] = (a'[0] + 19 * carry) % 2^51`
      `a[1] = a'[1] + (a'[0] + 19 * carry) / 2^51`
      `a[2] = a'[2]`
      `a[3] = a'[3]`
      `a[4] = a'[4]`

    Limb bounds (`ha''_lt`):
      `a''[i] < 2^52 for all i`
    -/
    -- Conversion helpers
    have h_i55 : i55.val = a'[0]!.val + 19 * carry.val := by simp [*]; ring
    have ha6_0 : a6[0]!.val = a'[0]!.val + 19 * carry.val := by
      simp only [a6_post, Array.set_of_eq _ _ 0 (by scalar_tac)]; exact h_i55
    have ha6_1 : a6[1]!.val = a'[1]!.val := by
      simp only [a6_post, Array.set_of_ne_getElem! _ _ 1 0 (by scalar_tac) (by scalar_tac) (by omega)]
    have h56_val : i56.val = a6[0]!.val := by simp [*]
    have h_i57 : i57.val = (a'[0]!.val + 19 * carry.val) / 2 ^ 51 := by
      simp only [i57_post_1, Nat.shiftRight_eq_div_pow, h56_val, ha6_0]
    have h60_val : i60.val = a7[0]!.val := by simp [*]
    have h58_val : i58.val = a6[1]!.val := by simp [*]
    -- Array values after final reduction
    have ha''_0 : a''[0]!.val = (a'[0]!.val + 19 * carry.val) % 2 ^ 51 := by
      simp only [a''_post, Array.set_of_eq _ _ 0 (by scalar_tac)]
      simp only [i61_post_1, UScalar.val_and, h60_val]
      simp only [a7_post, Array.set_of_ne_getElem! _ _ 0 1 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [ha6_0]
      simp_all only [Nat.and_two_pow_sub_one_eq_mod]
    have ha''_1 : a''[1]!.val = a'[1]!.val + (a'[0]!.val + 19 * carry.val) / 2 ^ 51 := by
      simp only [a''_post, Array.set_of_ne_getElem! _ _ 1 0 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a7_post, Array.set_of_eq _ _ 1 (by scalar_tac)]
      simp only [i59_post, h58_val, ha6_1, h_i57]
    have ha''_2 : a''[2]!.val = a'[2]!.val := by
      simp only [a''_post, Array.set_of_ne_getElem! _ _ 2 0 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a7_post, Array.set_of_ne_getElem! _ _ 2 1 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a6_post, Array.set_of_ne_getElem! _ _ 2 0 (by scalar_tac) (by scalar_tac) (by omega)]
    have ha''_3 : a''[3]!.val = a'[3]!.val := by
      simp only [a''_post, Array.set_of_ne_getElem! _ _ 3 0 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a7_post, Array.set_of_ne_getElem! _ _ 3 1 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a6_post, Array.set_of_ne_getElem! _ _ 3 0 (by scalar_tac) (by scalar_tac) (by omega)]
    have ha''_4 : a''[4]!.val = a'[4]!.val := by
      simp only [a''_post, Array.set_of_ne_getElem! _ _ 4 0 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a7_post, Array.set_of_ne_getElem! _ _ 4 1 (by scalar_tac) (by scalar_tac) (by omega)]
      simp only [a6_post, Array.set_of_ne_getElem! _ _ 4 0 (by scalar_tac) (by scalar_tac) (by omega)]
    --
    progress as ⟨ k1, k1_post_1, k1_post_2 ⟩
    -- Recursive call: pow2k_loop k1 a''
    -- Limb bounds for a'': all < 2^52
    have ha''_lt : ∀ i < 5, a''[i]!.val < 2 ^ 52 := by
      intro i hi; interval_cases i
      · rw [ha''_0]; have := Nat.mod_lt (a'[0]!.val + 19 * carry.val) (show 0 < 2 ^ 51 by positivity); omega
      · rw [ha''_1, ha'_1]
        have hmod : c1'.val % 2 ^ 51 < 2 ^ 51 := Nat.mod_lt _ (by positivity)
        have hdiv : (a'[0]!.val + 19 * carry.val) / 2 ^ 51 ≤ 2 ^ 13 - 1 := by
          have : a'[0]!.val + 19 * carry.val = i55.val := h_i55.symm
          rw [this]
          have : i55.val < 2 ^ 64 := by scalar_tac
          omega
        omega
      · rw [ha''_2, ha'_2]; have := Nat.mod_lt c2'.val (show 0 < 2 ^ 51 by positivity); omega
      · rw [ha''_3, ha'_3]; have := Nat.mod_lt c3'.val (show 0 < 2 ^ 51 by positivity); omega
      · rw [ha''_4, ha'_4]; have := Nat.mod_lt c4'.val (show 0 < 2 ^ 51 by positivity); omega
    --
    have ha''_54 : ∀ i < 5, a''[i]!.val < 2 ^ 54 :=
      fun i hi => by have := ha''_lt i hi; omega
    progress with pow2k_loop_spec as ⟨ res, res_post_1, res_post_2 ⟩
    -- Clear everything no longer needed
    clear * - pow2k_loop_spec k a ha hlt a'' carry a' ha''_0 ha''_1 ha''_2 ha''_3 ha''_4 ha''_lt
      ha'_0 ha'_1 ha'_2 ha'_3 ha'_4 c0 c1 c2 c3 c4 c1' c2' c3' c4' a_pow_two
      hc1'_eq hc2'_eq hc3'_eq hc4'_eq hcarry_val k1 k1_post_1 k1_post_2 res res_post_1 res_post_2
    -- Prove the post conditions using what was already established
    constructor
    · -- Field51_as_Nat res ≡ (Field51_as_Nat a)^(2^k.val) [MOD p]
      have hsq : Field51_as_Nat a'' ≡ (Field51_as_Nat a)^2 [MOD p] := by
        -- Strategy: show Field51_as_Nat a'' + carry.val * p = c0 + 2^51*c1 + ... + 2^204*c4
        -- Then conclude ModEq, and chain with a_pow_two.
        -- Step A: Field51_as_Nat a'' = (a'[0]+19*carry) + 2^51*a'[1]+2^102*a'[2]+2^153*a'[3]+2^204*a'[4]
        have hf_a'' : Field51_as_Nat a'' =
            (a'[0]!.val + 19 * carry.val) + 2^51 * a'[1]!.val + 2^102 * a'[2]!.val +
            2^153 * a'[3]!.val + 2^204 * a'[4]!.val := by
          unfold Field51_as_Nat
          simp only [Finset.sum_range_succ, Finset.sum_range_zero]
          rw [ha''_0, ha''_1, ha''_2, ha''_3, ha''_4]
          have := Nat.mod_add_div (a'[0]!.val + 19 * carry.val) (2 ^ 51)
          omega
        -- Step B: Carry chain conservation
        have h_chain : c0.val + 2^51 * c1.val + 2^102 * c2.val + 2^153 * c3.val + 2^204 * c4.val =
            a'[0]!.val + 2^51 * a'[1]!.val + 2^102 * a'[2]!.val + 2^153 * a'[3]!.val + 2^204 * a'[4]!.val +
            2^255 * carry.val :=
          carry_chain_eq c0.val c1.val c2.val c3.val c4.val
            a'[0]!.val a'[1]!.val a'[2]!.val a'[3]!.val a'[4]!.val carry.val c1'.val c2'.val c3'.val c4'.val
            ha'_0 ha'_1 ha'_2 ha'_3 ha'_4 hc1'_eq hc2'_eq hc3'_eq hc4'_eq hcarry_val
        -- Step C: Field51_as_Nat a'' + carry * p = c0 + ... + 2^204*c4
        have h_key : Field51_as_Nat a'' + carry.val * p =
            c0.val + 2^51 * c1.val + 2^102 * c2.val + 2^153 * c3.val + 2^204 * c4.val := by
          rw [hf_a'', h_chain]; unfold p; omega
        -- Step D: Conclude ModEq (from h_key: a''_nat + carry*p = c_sum)
        exact (modeq_of_add_mul_eq _ _ carry.val p h_key).trans a_pow_two
      have hpow := Nat.ModEq.pow (2^k1.val) hsq
      apply Nat.ModEq.trans res_post_1 hpow |>.trans
      rw [← pow_mul]
      have hk_pos : k.val ≥ 1 := by omega
      have : k1.val = k.val - 1 := by scalar_tac
      rw [this]
      have h2k : 2 * 2 ^ (k.val - 1) = 2 ^ k.val := by
        conv_rhs => rw [← Nat.sub_add_cancel hk_pos, Nat.pow_succ']
      rw [h2k]
    · -- if k.val = 0 then res = a else ∀ i < 5, res[i]!.val < 2^52
      -- We're in isTrue case, so k.val ≠ 0
      simp only [show k.val ≠ 0 by omega]
      -- res_post_2: if k1.val = 0 then res = a'' else ∀ i < 5, res[i]!.val < 2^52
      by_cases hk1 : k1.val = 0
      · -- k1 = 0: res = a'', need a''[i] < 2^52
        simp only [hk1] at res_post_2
        rw [res_post_2]
        exact ha''_lt
      · -- k1 ≠ 0: directly from recursive postcondition
        simp only [hk1, ite_false] at res_post_2
        exact res_post_2
  case isFalse hge =>
    progress*
    have : k.val = 0 := by scalar_tac
    simpa [this] using Nat.ModEq.trans rfl rfl
  termination_by k.val
  decreasing_by scalar_decr_tac

@[progress]
theorem pow2k_spec (self : Array U64 5#usize) (k : U32) (_ : 0 < k.val)
    (_ : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow2k self k ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (Field51_as_Nat self)^(2^k.val) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold pow2k
  progress*
  exact ⟨by assumption, by grind⟩

end curve25519_dalek.backend.serial.u64.field.FieldElement51
