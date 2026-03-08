/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

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

-- /-- Compute the 5 limbs of a² (before carry propagation) using radix-2^51 squaring.
--     Uses the identity 2^255 ≡ 19 (mod p) to reduce overflow terms. -/
-- def compute_square_limbs (a : Array U64 5#usize) : Result (U128 × U128 × U128 × U128 × U128) := do
--   let a0 := a[0]!
--   let a1 := a[1]!
--   let a2 := a[2]!
--   let a3 := a[3]!
--   let a4 := a[4]!
--   let a3_19 ← 19#u64 * a3
--   let a4_19 ← 19#u64 * a4
--   -- c0 = a0² + 2*(a1*a4_19 + a2*a3_19)
--   let t0 ← pow2k.m a0 a0
--   let t1 ← pow2k.m a1 a4_19
--   let t2 ← pow2k.m a2 a3_19
--   let t3 ← t1 + t2
--   let t4 ← 2#u128 * t3
--   let c0 ← t0 + t4
--   -- c1 = a3*a3_19 + 2*(a0*a1 + a2*a4_19)
--   let t5 ← pow2k.m a3 a3_19
--   let t6 ← pow2k.m a0 a1
--   let t7 ← pow2k.m a2 a4_19
--   let t8 ← t6 + t7
--   let t9 ← 2#u128 * t8
--   let c1 ← t5 + t9
--   -- c2 = a1² + 2*(a0*a2 + a4*a3_19)
--   let t10 ← pow2k.m a1 a1
--   let t11 ← pow2k.m a0 a2
--   let t12 ← pow2k.m a4 a3_19
--   let t13 ← t11 + t12
--   let t14 ← 2#u128 * t13
--   let c2 ← t10 + t14
--   -- c3 = a4*a4_19 + 2*(a0*a3 + a1*a2)
--   let t15 ← pow2k.m a4 a4_19
--   let t16 ← pow2k.m a0 a3
--   let t17 ← pow2k.m a1 a2
--   let t18 ← t16 + t17
--   let t19 ← 2#u128 * t18
--   let c3 ← t15 + t19
--   -- c4 = a2² + 2*(a0*a4 + a1*a3)
--   let t20 ← pow2k.m a2 a2
--   let t21 ← pow2k.m a0 a4
--   let t22 ← pow2k.m a1 a3
--   let t23 ← t21 + t22
--   let t24 ← 2#u128 * t23
--   let c4 ← t20 + t24
--   ok (c0, c1, c2, c3, c4)

/-- Bound for sum of two cross-products with 19x multipliers in squaring. -/
lemma cross_product_bound (a1 a2 a3 a4 : ℕ)
    (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a1 * (19 * a4) + a2 * (19 * a3) ≤ U128.max := by
  have : a1 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (38 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for 2 * (sum of two cross-products) -/
lemma two_cross_product_bound (a1 a2 a3 a4 : ℕ)
    (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    2 * (a1 * (19 * a4) + a2 * (19 * a3)) ≤ U128.max := by
  have : a1 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (76 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c0 = a0² + 2*(cross products) -/
lemma c0_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)) ≤ U128.max := by
  have : a0 * a0 < 2 ^ 108 := by nlinarith
  have : a1 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (77 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for intermediate sum: a*b + c*(19*d) -/
lemma intermediate_sum_bound (a b c d : ℕ)
    (ha : a < 2 ^ 54) (hb : b < 2 ^ 54) (hc : c < 2 ^ 54) (hd : d < 2 ^ 54) :
    a * b + c * (19 * d) ≤ U128.max := by
  have : a * b < 2 ^ 108 := by nlinarith
  have : c * (19 * d) < 19 * 2 ^ 108 := by nlinarith
  have : (20 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for intermediate sum: a*b + c*d (no 19x factor) -/
lemma intermediate_sum_bound' (a b c d : ℕ)
    (ha : a < 2 ^ 54) (hb : b < 2 ^ 54) (hc : c < 2 ^ 54) (hd : d < 2 ^ 54) :
    a * b + c * d ≤ U128.max := by
  have : a * b < 2 ^ 108 := by nlinarith
  have : c * d < 2 ^ 108 := by nlinarith
  have : (2 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for 2 * intermediate sum: 2*(a*b + c*(19*d)) -/
lemma two_intermediate_sum_bound (a b c d : ℕ)
    (ha : a < 2 ^ 54) (hb : b < 2 ^ 54) (hc : c < 2 ^ 54) (hd : d < 2 ^ 54) :
    2 * (a * b + c * (19 * d)) ≤ U128.max := by
  have : a * b < 2 ^ 108 := by nlinarith
  have : c * (19 * d) < 19 * 2 ^ 108 := by nlinarith
  have : (40 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for 2 * intermediate sum: 2*(a*b + c*d) (no 19x factor) -/
lemma two_intermediate_sum_bound' (a b c d : ℕ)
    (ha : a < 2 ^ 54) (hb : b < 2 ^ 54) (hc : c < 2 ^ 54) (hd : d < 2 ^ 54) :
    2 * (a * b + c * d) ≤ U128.max := by
  have : a * b < 2 ^ 108 := by nlinarith
  have : c * d < 2 ^ 108 := by nlinarith
  have : (4 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c1 = a3*(19*a3) + 2*(a0*a1 + a2*(19*a4)) -/
lemma c1_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4)) ≤ U128.max := by
  have : a3 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a1 < 2 ^ 108 := by nlinarith
  have : a2 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : (59 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c2 = a1² + 2*(a0*a2 + a4*(19*a3)) -/
lemma c2_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3)) ≤ U128.max := by
  have : a1 * a1 < 2 ^ 108 := by nlinarith
  have : a0 * a2 < 2 ^ 108 := by nlinarith
  have : a4 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (41 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c3 = a4*(19*a4) + 2*(a0*a3 + a1*a2) -/
lemma c3_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2) ≤ U128.max := by
  have : a4 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a3 < 2 ^ 108 := by nlinarith
  have : a1 * a2 < 2 ^ 108 := by nlinarith
  have : (23 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c4 = a2² + 2*(a0*a4 + a1*a3) -/
lemma c4_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a2 * a2 + 2 * (a0 * a4 + a1 * a3) ≤ U128.max := by
  have : a2 * a2 < 2 ^ 108 := by nlinarith
  have : a0 * a4 < 2 ^ 108 := by nlinarith
  have : a1 * a3 < 2 ^ 108 := by nlinarith
  have : (5 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

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

-- @[local simp]
-- theorem shiftLeft_54 : 1 <<< 54 % U64.size = 2^54 := by scalar_tac

/-- The final carry bound: if carry ≤ (2^64 - 2^51)/19 then 2^51 + 19*carry < 2^64. -/
lemma carry_mul_bound (carry_val : ℕ) (h : carry_val ≤ (2 ^ 64 - 2 ^ 51) / 19) :
    2 ^ 51 + 19 * carry_val < 2 ^ 64 := by
  have hle := Nat.mul_le_mul_right 19 h
  have hdiv : 19 * ((2 ^ 64 - 2 ^ 51) / 19) ≤ 2 ^ 64 - 2 ^ 51 := Nat.mul_div_le _ _
  omega


-- /-- The square limbs represent a² in radix-2^51 form modulo p.
--     c0 + 2^51*c1 + 2^102*c2 + 2^153*c3 + 2^204*c4 ≡ (Field51_as_Nat a)² [MOD p] -/
-- @[progress]
-- theorem compute_square_limbs_spec (a : Array U64 5#usize)
--     (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
--     ∃ c0 c1 c2 c3 c4 : U128, compute_square_limbs a = ok (c0, c1, c2, c3, c4) ∧
--     (c0.val + 2^51 * c1.val + 2^102 * c2.val + 2^153 * c3.val + 2^204 * c4.val)
--       ≡ (Field51_as_Nat a)^2 [MOD p] := by
--   unfold compute_square_limbs
--   have := ha 0 (by simp)
--   have := ha 1 (by simp)
--   have := ha 2 (by simp)
--   have := ha 3 (by simp)
--   have := ha 4 (by simp)
--   progress*
--   have := decompose a[0]!.val a[1]!.val a[2]!.val a[3]!.val a[4]!.val
--   use c0; use c1; use c2; use c3; use c4
--   refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
--   simp_all [-Nat.reducePow, Field51_as_Nat, Finset.sum_range_succ, Nat.ModEq]

set_option maxHeartbeats 1000000 in
-- progress* needs this
@[progress]
theorem pow2k_loop_spec (k' : U32) (a : Array U64 5#usize) (hk : 0 < k'.val)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    pow2k_loop k' a ⦃ (result : Std.Array U64 5#usize) =>
      Field51_as_Nat result ≡ (Field51_as_Nat a)^(2^k'.val) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold pow2k_loop
  have : k' > 0#u32 := by scalar_tac
  split
  case isTrue hlt =>

    -- Progress through the loop body to the 1st halt point, name only c0 c1 c2 c3 c4
    iterate 12 progress
    let* ⟨ c0, _ ⟩ ← U128.add_spec
    iterate 5 progress
    let* ⟨ c1, _ ⟩ ← U128.add_spec
    iterate 5 progress
    let* ⟨ c2, _ ⟩ ← U128.add_spec
    iterate 5 progress
    let* ⟨ c3, _ ⟩ ← U128.add_spec
    iterate 5 progress
    let* ⟨ c4, _ ⟩ ← U128.add_spec
    -- Arrived at the 1st halt point

    /-
    Stage 1:  The 5 intermediate products (c0-c4) have been computed (l.501 of source code)

    c0 = a[0]² + 2·(a[1]·(19·a[4]) + a[2]·(19·a[3])) = a[0]² + 38·(a[1]·a[4] + a[2]·a[3])
    c1 = (19·a[3])·a[3] + 2·(a[0]·a[1] + a[2]·(19·a[4])) = 19·a[3]² + 2·a[0]·a[1] + 38·a[2]·a[4]
    c2 = a[1]² + 2·(a[0]·a[2] + a[4]·(19·a[3])) = a[1]² + 2·a[0]·a[2] + 38·a[3]·a[4]
    c3 = (19·a[4])·a[4] + 2·(a[0]·a[3] + a[1]·a[2]) = 19·a[4]² + 2·a[0]·a[3] + 2·a[1]·a[2]
    c4 = a[2]² + 2·(a[0]·a[4] + a[1]·a[3]) = a[2]² + 2·a[0]·a[4] + 2·a[1]·a[3]
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
      simp_all [-Nat.reducePow, Field51_as_Nat, Finset.sum_range_succ, Nat.ModEq]

    -- NOTE: We can't use clear * - it kills the IH needed for recursion
    -- TODO: Find a convenient way to clear all the hypotheses which are no longer required
    rename_i wp0 eq0 wp1 eq1 wp2 eq2 wp3 eq3 wp4
    clear i3_post i5_post i7_post i8_post i9_post i10_post i11_post i12_post i13_post i14_post
      i15_post i16_post i17_post i18_post i19_post i20_post i21_post i22_post i23_post i24_post
      i25_post i26_post i27_post i28_post i29_post a3_19_post a4_19_post wp0 eq0 wp1 eq1 wp2 eq2 wp3
      eq3 wp4 this i3 i5 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i26
      i27 i28 a3_19 a4_19 hlt

    -- Continue to the 2nd halt point
    let* ⟨ i30, i30_post_1, i30_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
    let* ⟨ i31, i31_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ i32, i32_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ c11, c11_post ⟩ ← U128.add_spec
    let* ⟨ i33, i33_post ⟩ ← UScalar.cast.progress_spec
    progress with pow2k.LOW_51_BIT_MASK_spec
    let* ⟨ i34, i34_post_1, i34_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ a1, a1_post ⟩ ← Array.update_spec
    let* ⟨ i35, i35_post_1, i35_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
    let* ⟨ i36, i36_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ i37, i37_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ c21, c21_post ⟩ ← U128.add_spec
    let* ⟨ i38, i38_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ i39, i39_post_1, i39_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ a2, a2_post ⟩ ← Array.update_spec
    let* ⟨ i40, i40_post_1, i40_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
    let* ⟨ i41, i41_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ i42, i42_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ c31, c31_post ⟩ ← U128.add_spec
    let* ⟨ i43, i43_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ i44, i44_post_1, i44_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ a3, a3_post ⟩ ← Array.update_spec
    let* ⟨ i45, i45_post_1, i45_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
    let* ⟨ i46, i46_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ i47, i47_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ c41, c41_post ⟩ ← U128.add_spec
    let* ⟨ i48, i48_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ i49, i49_post_1, i49_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ a4, a4_post ⟩ ← Array.update_spec
    let* ⟨ i50, i50_post_1, i50_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
    let* ⟨ carry, carry_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ i51, i51_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ i52, i52_post_1, i52_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ a5, a5_post ⟩ ← Array.update_spec
    -- We are at the 2nd halt point

    -- Stage 2: After carry propagation (l.532 of source code)

    have hcarry0_fits : c0.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c0.val hc0'
    have hc11_bound : c11.val < 2 ^ 115 := by sorry
    have hcarry1_fits : c11.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c11.val (by grind)
    have hc21_bound : c21.val < 2 ^ 115 := by sorry
    have hcarry2_fits : c21.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c21.val hc21_bound
    have hc31_bound : c31.val < 2 ^ 115 := by sorry
    have hcarry3_fits : c31.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c31.val hc31_bound
    have hc41_bound : c41.val < 2 ^ 115 := by sorry
    have hcarry4_fits : c41.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c41.val hc41_bound

    /-
    Define intermediate carry-propagated values:
    c1' = c1 + ⌈c0⌉₅₁
    c2' = c2 + ⌈c1'⌉₅₁
    c3' = c3 + ⌈c2'⌉₅₁
    c4' = c4 + ⌈c3'⌉₅₁

    At this stage we have:
    a[0] = ⌊c0⌋₅₁
    a[1] = ⌊c1'⌋₅₁
    a[2] = ⌊c2'⌋₅₁
    a[3] = ⌊c3'⌋₅₁
    a[4] = ⌊c4'⌋₅₁
    carry = ⌈c4'⌉₅₁
    -/

    -- c11 = c1 + carry from c0
    have hc11' : c11.val = c1.val + c0.val / 2 ^ 51 := by
      simp only [c11_post, i32_post, i31_post, i30_post_1, UScalar.cast_val_eq,
        UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
      omega
    -- c21 = c2 + carry from c11
    have hc21' : c21.val = c2.val + c11.val / 2 ^ 51 := by
      simp only [c21_post, i37_post, i36_post, i35_post_1, UScalar.cast_val_eq,
        UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
      omega
    -- c31 = c3 + carry from c21
    have hc31' : c31.val = c3.val + c21.val / 2 ^ 51 := by
      simp only [c31_post, i42_post, i41_post, i40_post_1, UScalar.cast_val_eq,
        UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
      omega
    -- c41 = c4 + carry from c31
    have hc41' : c41.val = c4.val + c31.val / 2 ^ 51 := by
      simp only [c41_post, i47_post, i46_post, i45_post_1, UScalar.cast_val_eq,
        UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
      omega

    -- Array values after carry propagation
    have ha5_0 : a5[0]!.val = c0.val % 2 ^ 51 := by sorry
    have ha5_1 : a5[1]!.val = c11.val % 2 ^ 51 := by sorry
    have ha5_2 : a5[2]!.val = c21.val % 2 ^ 51 := by sorry
    have ha5_3 : a5[3]!.val = c31.val % 2 ^ 51 := by sorry
    have ha5_4 : a5[4]!.val = c41.val % 2 ^ 51 := by sorry
    have hcarry_val : carry.val = c41.val / 2 ^ 51 := by
      simp only [carry_post, i50_post_1, UScalar.cast_val_eq, UScalarTy.numBits,
        Nat.shiftRight_eq_div_pow]
      omega

    -- Continue until the end of the function
    let* ⟨ i53, i53_post ⟩ ← U64.mul_spec
    let* ⟨ i54, i54_post ⟩ ← Array.index_usize_spec
    let* ⟨ i55, i55_post ⟩ ← U64.add_spec
    let* ⟨ a6, a6_post ⟩ ← Array.update_spec
    let* ⟨ i56, i56_post ⟩ ← Array.index_usize_spec
    let* ⟨ i57, i57_post_1, i57_post_2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i58, i58_post ⟩ ← Array.index_usize_spec
    -- Progress needs to apply `U64.add_spec` but gets stuck trying to solve the precondition
    apply spec_bind
    · apply U64.add_spec
      sorry  -- overflow side condition
    intro i59 i59_post
    -- let* ⟨ i59, i59_post ⟩ ← U64.add_spec
    let* ⟨ a7, a7_post ⟩ ← Array.update_spec
    let* ⟨ i60, i60_post ⟩ ← Array.index_usize_spec
    let* ⟨ i61, i61_post_1, i61_post_2 ⟩ ← UScalar.and_spec
    let* ⟨ a8, a8_post ⟩ ← Array.update_spec

    -- Stage 3: Final reduction (l.552 of source file)

    /-
    Let the values from stage 2 be denoted with subscript ₂. Now we have:
    a[0] = ⌊a[0]₂ + 19·carry⌋₅₁
    a[1] = a[1]₂ + ⌈a[0]₂ + 19·carry⌉₅₁
    a[2] = a[2]₂
    a[3] = a[3]₂
    a[4] = a[4]₂
    -/

    -- Array values after final reduction
    have ha8_0 : a8[0]!.val = (a5[0]!.val + 19 * carry.val) % 2 ^ 51 := by sorry
    have ha8_1 : a8[1]!.val = a5[1]!.val + (a5[0]!.val + 19 * carry.val) / 2 ^ 51 := by sorry
    have ha8_2 : a8[2]!.val = a5[2]!.val := by sorry
    have ha8_3 : a8[3]!.val = a5[3]!.val := by sorry
    have ha8_4 : a8[4]!.val = a5[4]!.val := by sorry

    let* ⟨ k1, k1_post_1, k1_post_2 ⟩ ← U32.sub_spec

    progress as ⟨ res, res_post_1, res_post_2 ⟩
    · -- side condition: 0 < k1.val
      -- simp only [*]
      sorry
    · -- side condition: ∀ i < 5, a8[i]!.val < 2 ^ 54
      intro i hi
      interval_cases i
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
    -- Now we have res with res_post_1 and res_post_2
    constructor
    · -- Main equality: Field51_as_Nat res ≡ (Field51_as_Nat a)^(2^k) [MOD p]
      -- res satisfies: Field51_as_Nat res ≡ (Field51_as_Nat a8)^(2^(k-1)) [MOD p]
      -- a8 ≡ a^2 [MOD p], so res ≡ (a^2)^(2^(k-1)) = a^(2^k) [MOD p]
      have hsq : Field51_as_Nat a8 ≡ (Field51_as_Nat a)^2 [MOD p] := by
        sorry
      simp only [*] at res_post_1
      -- have hpow := Nat.ModEq.pow (2^(k-1)) hsq
      -- apply Nat.ModEq.trans res_post_1 hpow |>.trans
      -- rw [← pow_mul]
      -- have hk_pos : k ≥ 1 := by omega
      -- have h2k : 2 * 2 ^ (k - 1) = 2 ^ k := by
      --   conv_rhs => rw [← Nat.sub_add_cancel hk_pos, Nat.pow_succ']
      -- rw [h2k]
      sorry
    · assumption

  case isFalse hge =>
    progress*

/-

  -- Now handle the recursive call
  -- The recursion: pow2k_loop (k-1) a8 where a8 is the squared result
  -- Base case (k=1): k1=0, next iteration returns immediately with ok a8
  -- Recursive case (k>1): k1>0, continues squaring
  by_cases hk1 : k'.val = 1
  · -- k = 1 case: k1 = 0, so recursive call returns immediately
    -- subst hk1
    have hk1_zero : ¬(k1 > 0#u32) := by scalar_tac
    unfold pow2k_loop
    simp only [hk1_zero, ↓reduceIte, progress_simps]
    constructor
    · -- Main equality for k=1: a8 ≡ a^2 [MOD p]
      sorry
    · -- Bounds: each limb < 2^52
      sorry
  · -- k > 1 case: k1 > 0, recursive call does more squaring
    have hk1_pos : 0 < k'.val - 1 := by omega
    have ha8 : ∀ i < 5, a8[i]!.val < 2 ^ 54 := by sorry
    let* ⟨ res, res_post_1, res_post_2 ⟩ ← pow2k_loop_spec
    constructor
    · -- Main equality: Field51_as_Nat res ≡ (Field51_as_Nat a)^(2^k) [MOD p]
      -- res satisfies: Field51_as_Nat res ≡ (Field51_as_Nat a8)^(2^(k-1)) [MOD p]
      -- a8 ≡ a^2 [MOD p], so res ≡ (a^2)^(2^(k-1)) = a^(2^k) [MOD p]
      have hsq : Field51_as_Nat a8 ≡ (Field51_as_Nat a)^2 [MOD p] := by
        sorry
      simp only [eqk] at res_post_1
      have hpow := Nat.ModEq.pow (2^(k-1)) hsq
      apply Nat.ModEq.trans res_post_1 hpow |>.trans
      rw [← pow_mul]
      have hk_pos : k ≥ 1 := by omega
      have h2k : 2 * 2 ^ (k - 1) = 2 ^ k := by
        conv_rhs => rw [← Nat.sub_add_cancel hk_pos, Nat.pow_succ']
      rw [h2k]
    · assumption

    -/
  termination_by k'.val
  decreasing_by scalar_decr_tac; sorry

@[progress]
theorem pow2k_spec (self : Array U64 5#usize) (k : U32) (hk : 0 < k.val)
    (ha : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow2k self k ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (Field51_as_Nat self)^(2^k.val) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold pow2k
  progress*

end curve25519_dalek.backend.serial.u64.field.FieldElement51
