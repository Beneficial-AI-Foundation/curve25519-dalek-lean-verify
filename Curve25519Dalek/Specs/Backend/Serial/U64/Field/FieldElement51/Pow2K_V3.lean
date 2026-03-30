/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

/-! # Specification for `FieldElement51::pow2k`.

This function computes the 2^k-th power of a field element.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

## Source code

```rust
    /// Given `k > 0`, return `self^(2^k)`.
    pub fn pow2k(&self, mut k: u32) -> FieldElement51 {
        debug_assert!( k > 0 );
        fn m(x: u64, y: u64) -> u128 { (x as u128) * (y as u128) }
        let mut a: [u64; 5] = self.0;
        while k > 0 {
            let a3_19 = 19 * a[3];
            let a4_19 = 19 * a[4];
            let     c0: u128 = m(a[0],  a[0]) + 2*( m(a[1], a4_19) + m(a[2], a3_19) );
            let mut c1: u128 = m(a[3], a3_19) + 2*( m(a[0],  a[1]) + m(a[2], a4_19) );
            let mut c2: u128 = m(a[1],  a[1]) + 2*( m(a[0],  a[2]) + m(a[4], a3_19) );
            let mut c3: u128 = m(a[4], a4_19) + 2*( m(a[0],  a[3]) + m(a[1],  a[2]) );
            let mut c4: u128 = m(a[2],  a[2]) + 2*( m(a[0],  a[4]) + m(a[1],  a[3]) );
            const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;
            c1 += ((c0 >> 51) as u64) as u128;  a[0] = (c0 as u64) & LOW_51_BIT_MASK;
            c2 += ((c1 >> 51) as u64) as u128;  a[1] = (c1 as u64) & LOW_51_BIT_MASK;
            c3 += ((c2 >> 51) as u64) as u128;  a[2] = (c2 as u64) & LOW_51_BIT_MASK;
            c4 += ((c3 >> 51) as u64) as u128;  a[3] = (c3 as u64) & LOW_51_BIT_MASK;
            let carry: u64 = (c4 >> 51) as u64;  a[4] = (c4 as u64) & LOW_51_BIT_MASK;
            a[0] += carry * 19;
            a[1] += a[0] >> 51;
            a[0] &= LOW_51_BIT_MASK;
            k -= 1;
        }
        FieldElement51(a)
    }
```

## Proof strategy: Fold theorem decomposition

The loop body is decomposed into 3 helper functions, each with a fold theorem and `@[step]` spec.

### Stage 1 — Squaring (`square_stage`)

Computes the 5 intermediate 128-bit products c0–c4 from the input limbs:
  `c0 = a[0]² + 2·(a[1]·(19·a[4]) + a[2]·(19·a[3]))`
  `c1 = (19·a[3])·a[3] + 2·(a[0]·a[1] + a[2]·(19·a[4]))`
  `c2 = a[1]² + 2·(a[0]·a[2] + a[4]·(19·a[3]))`
  `c3 = (19·a[4])·a[4] + 2·(a[0]·a[3] + a[1]·a[2])`
  `c4 = a[2]² + 2·(a[0]·a[4] + a[1]·a[3])`

Bounds: `c0 < 2^115`, ..., `c4 < 2^115`.
Algebraic identity: `c0 + 2^51·c1 + 2^102·c2 + 2^153·c3 + 2^204·c4 ≡ (Field51_as_Nat a)² [MOD p]`.

### Stage 2 — Carry propagation (`carry_prop_stage`)

Propagates carries through c0–c4:
```rust
  c1 += (c0 >> 51) as u64;  a[0] = (c0 as u64) & LOW_51_BIT_MASK;
  c2 += (c1 >> 51) as u64;  a[1] = (c1 as u64) & LOW_51_BIT_MASK;
  c3 += (c2 >> 51) as u64;  a[2] = (c2 as u64) & LOW_51_BIT_MASK;
  c4 += (c3 >> 51) as u64;  a[3] = (c3 as u64) & LOW_51_BIT_MASK;
  carry = (c4 >> 51) as u64; a[4] = (c4 as u64) & LOW_51_BIT_MASK;
```

With carry-propagated accumulators `c1' = c1 + c0/2^51`, ..., `c4' = c4 + c3'/2^51`:
  `a'[0] = c0 % 2^51`, `a'[1] = c1' % 2^51`, ..., `a'[4] = c4' % 2^51`
  `carry = c4' / 2^51`

Carry chain conservation: `c0 + 2^51·c1 + ... = a'[0] + 2^51·a'[1] + ... + 2^255·carry`.

### Stage 3 — Final reduction (`final_reduce_stage`)

Folds the carry back into the low limb:
```rust
  a[0] += carry * 19;
  a[1] += a[0] >> 51;
  a[0] &= LOW_51_BIT_MASK;
```

Output array values (writing `a''` for the result):
  `a''[0] = (a'[0] + 19·carry) % 2^51`
  `a''[1] = a'[1] + (a'[0] + 19·carry) / 2^51`
  `a''[2..4] = a'[2..4]`

Limb bounds: `a''[i] < 2^52` for all `i`.

### Fold mechanism

The fold theorems (`fold_square_stage`, `fold_carry_prop_stage`, `fold_final_reduce_stage`)
prove that the inline monadic code equals calls to the helpers. Each is proved by
`simp only [helper, bind_assoc_eq, bind_tc_ok]`. In `pow2k_loop_spec`, the three folds
are applied via `simp_rw [fold_*]`, collapsing the 90-line loop body into 3 helper calls.
Then `step*` applies the `@[step]` specs automatically.
-/

set_option linter.hashCommand false
#setup_aeneas_simps

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.v3

open curve25519_dalek.backend.serial.u64.field.FieldElement51 (pow2k pow2k_loop)
open curve25519_dalek.backend.serial.u64.field.FieldElement51.pow2k (m LOW_51_BIT_MASK)

@[step]
theorem m_spec (x y : U64) :
    m x y ⦃ (result : U128) => result.val = x.val * y.val ⦄ := by
  unfold m; step*

@[step]
theorem LOW_51_BIT_MASK_spec :
    LOW_51_BIT_MASK ⦃ (result : U64) => result.val = 2^51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK; step*

/-! ## Helper Functions -/

/-- Stage 1: Compute the 5 intermediate products for field squaring in radix-2^51. -/
def square_stage (a : Array U64 5#usize) : Result (U128 × U128 × U128 × U128 × U128) := do
  let i ← Array.index_usize a 3#usize
  let a3_19 ← 19#u64 * i
  let i1 ← Array.index_usize a 4#usize
  let a4_19 ← 19#u64 * i1
  let i2 ← Array.index_usize a 0#usize
  let i3 ← m i2 i2
  let i4 ← Array.index_usize a 1#usize
  let i5 ← m i4 a4_19
  let i6 ← Array.index_usize a 2#usize
  let i7 ← m i6 a3_19
  let i8 ← i5 + i7
  let i9 ← 2#u128 * i8
  let c0 ← i3 + i9
  let i10 ← m i a3_19
  let i11 ← m i2 i4
  let i12 ← m i6 a4_19
  let i13 ← i11 + i12
  let i14 ← 2#u128 * i13
  let c1 ← i10 + i14
  let i15 ← m i4 i4
  let i16 ← m i2 i6
  let i17 ← m i1 a3_19
  let i18 ← i16 + i17
  let i19 ← 2#u128 * i18
  let c2 ← i15 + i19
  let i20 ← m i1 a4_19
  let i21 ← m i2 i
  let i22 ← m i4 i6
  let i23 ← i21 + i22
  let i24 ← 2#u128 * i23
  let c3 ← i20 + i24
  let i25 ← m i6 i6
  let i26 ← m i2 i1
  let i27 ← m i4 i
  let i28 ← i26 + i27
  let i29 ← 2#u128 * i28
  let c4 ← i25 + i29
  ok (c0, c1, c2, c3, c4)

/-- Stage 2: Propagate carries through c0–c4. Returns `(array, carry, mask)`. -/
def carry_prop_stage (a : Array U64 5#usize) (c0 c1 c2 c3 c4 : U128) :
    Result (Array U64 5#usize × U64 × U64) := do
  let i30 ← c0 >>> 51#i32
  let i31 ← lift (UScalar.cast .U64 i30)
  let i32 ← lift (UScalar.cast .U128 i31)
  let c11 ← c1 + i32
  let i33 ← lift (UScalar.cast .U64 c0)
  let i34 ← LOW_51_BIT_MASK
  let i35 ← lift (i33 &&& i34)
  let a1 ← Array.update a 0#usize i35
  let i36 ← c11 >>> 51#i32
  let i37 ← lift (UScalar.cast .U64 i36)
  let i38 ← lift (UScalar.cast .U128 i37)
  let c21 ← c2 + i38
  let i39 ← lift (UScalar.cast .U64 c11)
  let i40 ← lift (i39 &&& i34)
  let a2 ← Array.update a1 1#usize i40
  let i41 ← c21 >>> 51#i32
  let i42 ← lift (UScalar.cast .U64 i41)
  let i43 ← lift (UScalar.cast .U128 i42)
  let c31 ← c3 + i43
  let i44 ← lift (UScalar.cast .U64 c21)
  let i45 ← lift (i44 &&& i34)
  let a3 ← Array.update a2 2#usize i45
  let i46 ← c31 >>> 51#i32
  let i47 ← lift (UScalar.cast .U64 i46)
  let i48 ← lift (UScalar.cast .U128 i47)
  let c41 ← c4 + i48
  let i49 ← lift (UScalar.cast .U64 c31)
  let i50 ← lift (i49 &&& i34)
  let a4 ← Array.update a3 3#usize i50
  let i51 ← c41 >>> 51#i32
  let carry ← lift (UScalar.cast .U64 i51)
  let i52 ← lift (UScalar.cast .U64 c41)
  let i53 ← lift (i52 &&& i34)
  let a5 ← Array.update a4 4#usize i53
  ok (a5, carry, i34)

/-- Stage 3: Fold carry back via `carry * 19`. Takes mask from `carry_prop_stage`. -/
def final_reduce_stage (a5 : Array U64 5#usize) (carry : U64) (i34 : U64) :
    Result (Array U64 5#usize) := do
  let i54 ← carry * 19#u64
  let i55 ← Array.index_usize a5 0#usize
  let i56 ← i55 + i54
  let a6 ← Array.update a5 0#usize i56
  let i57 ← Array.index_usize a6 0#usize
  let i58 ← i57 >>> 51#i32
  let i59 ← Array.index_usize a6 1#usize
  let i60 ← i59 + i58
  let a7 ← Array.update a6 1#usize i60
  let i61 ← Array.index_usize a7 0#usize
  let i62 ← lift (i61 &&& i34)
  let a8 ← Array.update a7 0#usize i62
  ok a8

/-! ## Fold Theorems -/

theorem fold_square_stage {α : Type} (a : Array U64 5#usize)
    (f : U128 → U128 → U128 → U128 → U128 → Result α) :
    (do let i ← Array.index_usize a 3#usize; let a3_19 ← 19#u64 * i
        let i1 ← Array.index_usize a 4#usize; let a4_19 ← 19#u64 * i1
        let i2 ← Array.index_usize a 0#usize; let i3 ← m i2 i2
        let i4 ← Array.index_usize a 1#usize; let i5 ← m i4 a4_19
        let i6 ← Array.index_usize a 2#usize; let i7 ← m i6 a3_19
        let i8 ← i5 + i7; let i9 ← 2#u128 * i8; let c0 ← i3 + i9
        let i10 ← m i a3_19; let i11 ← m i2 i4; let i12 ← m i6 a4_19
        let i13 ← i11 + i12; let i14 ← 2#u128 * i13; let c1 ← i10 + i14
        let i15 ← m i4 i4; let i16 ← m i2 i6; let i17 ← m i1 a3_19
        let i18 ← i16 + i17; let i19 ← 2#u128 * i18; let c2 ← i15 + i19
        let i20 ← m i1 a4_19; let i21 ← m i2 i; let i22 ← m i4 i6
        let i23 ← i21 + i22; let i24 ← 2#u128 * i23; let c3 ← i20 + i24
        let i25 ← m i6 i6; let i26 ← m i2 i1; let i27 ← m i4 i
        let i28 ← i26 + i27; let i29 ← 2#u128 * i28; let c4 ← i25 + i29
        f c0 c1 c2 c3 c4) =
    (do let r ← square_stage a; f r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) := by
  simp only [square_stage, bind_assoc_eq, bind_tc_ok]

theorem fold_carry_prop_stage {α : Type} (a : Array U64 5#usize) (c0 c1 c2 c3 c4 : U128)
    (f : Array U64 5#usize → U64 → U64 → Result α) :
    (do let i30 ← c0 >>> 51#i32; let i31 ← lift (UScalar.cast .U64 i30)
        let i32 ← lift (UScalar.cast .U128 i31); let c11 ← c1 + i32
        let i33 ← lift (UScalar.cast .U64 c0); let i34 ← LOW_51_BIT_MASK
        let i35 ← lift (i33 &&& i34); let a1 ← Array.update a 0#usize i35
        let i36 ← c11 >>> 51#i32; let i37 ← lift (UScalar.cast .U64 i36)
        let i38 ← lift (UScalar.cast .U128 i37); let c21 ← c2 + i38
        let i39 ← lift (UScalar.cast .U64 c11); let i40 ← lift (i39 &&& i34)
        let a2 ← Array.update a1 1#usize i40
        let i41 ← c21 >>> 51#i32; let i42 ← lift (UScalar.cast .U64 i41)
        let i43 ← lift (UScalar.cast .U128 i42); let c31 ← c3 + i43
        let i44 ← lift (UScalar.cast .U64 c21); let i45 ← lift (i44 &&& i34)
        let a3 ← Array.update a2 2#usize i45
        let i46 ← c31 >>> 51#i32; let i47 ← lift (UScalar.cast .U64 i46)
        let i48 ← lift (UScalar.cast .U128 i47); let c41 ← c4 + i48
        let i49 ← lift (UScalar.cast .U64 c31); let i50 ← lift (i49 &&& i34)
        let a4 ← Array.update a3 3#usize i50
        let i51 ← c41 >>> 51#i32; let carry ← lift (UScalar.cast .U64 i51)
        let i52 ← lift (UScalar.cast .U64 c41); let i53 ← lift (i52 &&& i34)
        let a5 ← Array.update a4 4#usize i53
        f a5 carry i34) =
    (do let r ← carry_prop_stage a c0 c1 c2 c3 c4; f r.1 r.2.1 r.2.2) := by
  simp only [carry_prop_stage, bind_assoc_eq, bind_tc_ok]

theorem fold_final_reduce_stage {α : Type} (a5 : Array U64 5#usize) (carry i34 : U64)
    (f : Array U64 5#usize → Result α) :
    (do let i54 ← carry * 19#u64
        let i55 ← Array.index_usize a5 0#usize; let i56 ← i55 + i54
        let a6 ← Array.update a5 0#usize i56
        let i57 ← Array.index_usize a6 0#usize; let i58 ← i57 >>> 51#i32
        let i59 ← Array.index_usize a6 1#usize; let i60 ← i59 + i58
        let a7 ← Array.update a6 1#usize i60
        let i61 ← Array.index_usize a7 0#usize
        let i62 ← lift (i61 &&& i34)
        let a8 ← Array.update a7 0#usize i62
        f a8) =
    (do let r ← final_reduce_stage a5 carry i34; f r) := by
  simp only [final_reduce_stage, bind_assoc_eq, bind_tc_ok]

/-! ## Bounds Lemmas -/

/-- c0 < 77 * 2^108 < 2^115 -/
private lemma c0_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)) < 2 ^ 115 := by
  have : a0 * a0 < 2 ^ 108 := by nlinarith
  have : a1 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (77 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c1 < 59 * 2^108 < 2^115 -/
private lemma c1_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4)) < 2 ^ 115 := by
  have : a3 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a1 < 2 ^ 108 := by nlinarith
  have : a2 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : (59 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c2 < 41 * 2^108 < 2^115 -/
private lemma c2_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3)) < 2 ^ 115 := by
  have : a1 * a1 < 2 ^ 108 := by nlinarith
  have : a0 * a2 < 2 ^ 108 := by nlinarith
  have : a4 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (41 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c3 < 23 * 2^108 < 2^115 -/
private lemma c3_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2) < 2 ^ 115 := by
  have : a4 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a3 < 2 ^ 108 := by nlinarith
  have : a1 * a2 < 2 ^ 108 := by nlinarith
  have : (23 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c4 < 5 * 2^108 < 2^115 -/
private lemma c4_lt_pow2_115 (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a2 * a2 + 2 * (a0 * a4 + a1 * a3) < 2 ^ 115 := by
  have : a2 * a2 < 2 ^ 108 := by nlinarith
  have : a0 * a4 < 2 ^ 108 := by nlinarith
  have : a1 * a3 < 2 ^ 108 := by nlinarith
  have : (5 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- Squaring in radix-2^51, mod p, key algebraic identity. -/
private lemma decompose (a0 a1 a2 a3 a4 : ℕ) :
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

/-- Carry chain conservation. -/
private lemma carry_chain_eq (c0 c1 c2 c3 c4 a0 a1 a2 a3 a4 carry c1' c2' c3' c4' : ℕ)
    (ha0 : a0 = c0 % 2 ^ 51) (ha1 : a1 = c1' % 2 ^ 51) (ha2 : a2 = c2' % 2 ^ 51)
    (ha3 : a3 = c3' % 2 ^ 51) (ha4 : a4 = c4' % 2 ^ 51)
    (hc1' : c1' = c1 + c0 / 2 ^ 51) (hc2' : c2' = c2 + c1' / 2 ^ 51)
    (hc3' : c3' = c3 + c2' / 2 ^ 51) (hc4' : c4' = c4 + c3' / 2 ^ 51)
    (hcarry : carry = c4' / 2 ^ 51) :
    c0 + 2^51*c1 + 2^102*c2 + 2^153*c3 + 2^204*c4 =
    a0 + 2^51*a1 + 2^102*a2 + 2^153*a3 + 2^204*a4 + 2^255*carry := by omega

/-- Generic carry chain bound. -/
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

/-! ## Helper Specs -/

@[step]
theorem square_stage_spec (a : Array U64 5#usize) (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    square_stage a ⦃ ((c0, c1, c2, c3, c4) : U128 × U128 × U128 × U128 × U128) =>
      c0.val = a[0]!.val * a[0]!.val + 2 *
        (a[1]!.val * (19 * a[4]!.val) + a[2]!.val * (19 * a[3]!.val)) ∧
      c1.val = a[3]!.val * (19 * a[3]!.val) + 2 *
        (a[0]!.val * a[1]!.val + a[2]!.val * (19 * a[4]!.val)) ∧
      c2.val = a[1]!.val * a[1]!.val + 2 * (a[0]!.val * a[2]!.val + a[4]!.val * (19 * a[3]!.val)) ∧
      c3.val = a[4]!.val * (19 * a[4]!.val) + 2 * (a[0]!.val * a[3]!.val + a[1]!.val * a[2]!.val) ∧
      c4.val = a[2]!.val * a[2]!.val + 2 * (a[0]!.val * a[4]!.val + a[1]!.val * a[3]!.val) ∧
      c0.val < 2 ^ 115 ∧ c1.val < 2 ^ 115 ∧ c2.val < 2 ^ 115 ∧
      c3.val < 2 ^ 115 ∧ c4.val < 2 ^ 115 ∧
      c1.val < 59 * 2 ^ 108 ∧ c2.val < 41 * 2 ^ 108 ∧
      c3.val < 23 * 2 ^ 108 ∧ c4.val < 5 * 2 ^ 108 ⦄ := by
  unfold square_stage
  simp only [step_simps]
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
  let* ⟨ a3_19, a3_19_post ⟩ ← U64.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
  let* ⟨ a4_19, a4_19_post ⟩ ← U64.mul_spec
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
  let* ⟨ i3, i3_post ⟩ ← m_spec
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
  let* ⟨ i5, i5_post ⟩ ← m_spec
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
  let* ⟨ i7, i7_post ⟩ ← m_spec
  let* ⟨ i8, i8_post ⟩ ← U128.add_spec
  let* ⟨ i9, i9_post ⟩ ← U128.mul_spec
  let* ⟨ c0, c0_post ⟩ ← U128.add_spec
  let* ⟨ i10, i10_post ⟩ ← m_spec
  let* ⟨ i11, i11_post ⟩ ← m_spec
  let* ⟨ i12, i12_post ⟩ ← m_spec
  let* ⟨ i13, i13_post ⟩ ← U128.add_spec
  let* ⟨ i14, i14_post ⟩ ← U128.mul_spec
  let* ⟨ c1, c1_post ⟩ ← U128.add_spec
  let* ⟨ i15, i15_post ⟩ ← m_spec
  let* ⟨ i16, i16_post ⟩ ← m_spec
  let* ⟨ i17, i17_post ⟩ ← m_spec
  let* ⟨ i18, i18_post ⟩ ← U128.add_spec
  let* ⟨ i19, i19_post ⟩ ← U128.mul_spec
  let* ⟨ c2, c2_post ⟩ ← U128.add_spec
  let* ⟨ i20, i20_post ⟩ ← m_spec
  let* ⟨ i21, i21_post ⟩ ← m_spec
  let* ⟨ i22, i22_post ⟩ ← m_spec
  let* ⟨ i23, i23_post ⟩ ← U128.add_spec
  let* ⟨ i24, i24_post ⟩ ← U128.mul_spec
  let* ⟨ c3, c3_post ⟩ ← U128.add_spec
  let* ⟨ i25, i25_post ⟩ ← m_spec
  let* ⟨ i26, i26_post ⟩ ← m_spec
  let* ⟨ i27, i27_post ⟩ ← m_spec
  let* ⟨ i28, i28_post ⟩ ← U128.add_spec
  let* ⟨ i29, i29_post ⟩ ← U128.mul_spec
  let* ⟨ c4, c4_post ⟩ ← U128.add_spec
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
  exact ⟨hc0, hc1, hc2, hc3, hc4,
    by rw [hc0]; exact c0_lt_pow2_115 _ _ _ _ _ (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp)),
    by rw [hc1]; exact c1_lt_pow2_115 _ _ _ _ _ (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp)),
    by rw [hc2]; exact c2_lt_pow2_115 _ _ _ _ _ (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp)),
    by rw [hc3]; exact c3_lt_pow2_115 _ _ _ _ _ (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp)),
    by rw [hc4]; exact c4_lt_pow2_115 _ _ _ _ _ (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp)),
    by rw [hc1]; exact c1_lt_tight _ _ _ _ _ (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp)),
    by rw [hc2]; exact c2_lt_tight _ _ _ _ _ (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp)),
    by rw [hc3]; exact c3_lt_tight _ _ _ _ _ (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp)),
    by rw [hc4]; exact c4_lt_tight _ _ _ _ _ (ha 0 (by simp)) (ha 1 (by simp)) (ha 2 (by simp)) (ha 3 (by simp)) (ha 4 (by simp))⟩

set_option maxHeartbeats 8000000 in
-- Required for step* through ~30 monadic operations
@[step]
theorem carry_prop_stage_spec (a : Array U64 5#usize) (c0 c1 c2 c3 c4 : U128)
    (hc0 : c0.val < 2 ^ 115) (_hc1 : c1.val < 2 ^ 115) (_hc2 : c2.val < 2 ^ 115)
    (_hc3 : c3.val < 2 ^ 115) (_hc4 : c4.val < 2 ^ 115)
    (hc1_tight : c1.val < 59 * 2 ^ 108) (hc2_tight : c2.val < 41 * 2 ^ 108)
    (hc3_tight : c3.val < 23 * 2 ^ 108) (hc4_tight : c4.val < 5 * 2 ^ 108) :
    carry_prop_stage a c0 c1 c2 c3 c4 ⦃ ((a', carry, _mask) : Array U64 5#usize × U64 × U64) =>
      a'[0]!.val = c0.val % 2 ^ 51 ∧
      a'[1]!.val = (c1.val + c0.val / 2 ^ 51) % 2 ^ 51 ∧
      a'[2]!.val = (c2.val + (c1.val + c0.val / 2 ^ 51) / 2 ^ 51) % 2 ^ 51 ∧
      a'[3]!.val = (c3.val + (c2.val + (c1.val + c0.val / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51 ∧
      a'[4]!.val = (c4.val + (c3.val + (c2.val + (c1.val + c0.val / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51 ∧
      carry.val = (c4.val + (c3.val + (c2.val + (c1.val + c0.val / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51 ∧
      _mask.val = 2 ^ 51 - 1 ∧
      carry.val < 6 * 2 ^ 57 ⦄ := by
  unfold carry_prop_stage
  simp only [step_simps]
  let* ⟨ i30, i30_post1, i30_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i31, i31_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i32, i32_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c11, c11_post ⟩ ← U128.add_spec
  let* ⟨ i33, i33_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i34, i34_post ⟩ ← LOW_51_BIT_MASK_spec
  let* ⟨ i35, i35_post1, i35_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a1, a1_post ⟩ ← Array.update_spec
  let* ⟨ i36, i36_post1, i36_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i37, i37_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i38, i38_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c21, c21_post ⟩ ← U128.add_spec
  let* ⟨ i39, i39_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i40, i40_post1, i40_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a2, a2_post ⟩ ← Array.update_spec
  let* ⟨ i41, i41_post1, i41_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i42, i42_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i43, i43_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c31, c31_post ⟩ ← U128.add_spec
  let* ⟨ i44, i44_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i45, i45_post1, i45_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a3, a3_post ⟩ ← Array.update_spec
  let* ⟨ i46, i46_post1, i46_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i47, i47_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i48, i48_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c41, c41_post ⟩ ← U128.add_spec
  let* ⟨ i49, i49_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i50, i50_post1, i50_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a4, a4_post ⟩ ← Array.update_spec
  let* ⟨ i51, i51_post1, i51_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ carry, carry_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i52, i52_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i53, i53_post1, i53_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a5, a5_post ⟩ ← Array.update_spec
  -- Interleaved carry chain: each step needs the previous carry-fits bound
  -- to eliminate the % 2^64 from the U128→U64→U128 cast chain.
  have hcarry0_fits : c0.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c0.val hc0
  -- c11 = c1 + carry from c0
  have hc11_eq : c11.val = c1.val + c0.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  have hc11_bound : c11.val < 2 ^ 115 := by
    rw [hc11_eq]; exact carry_chain_lt_pow2_115 _ _ 59 hc1_tight hcarry0_fits (by omega)
  have hcarry1_fits : c11.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c11.val hc11_bound
  -- c21 = c2 + carry from c11
  have hc21_eq : c21.val = c2.val + c11.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  have hc21_bound : c21.val < 2 ^ 115 := by
    rw [hc21_eq]; exact carry_chain_lt_pow2_115 _ _ 41 hc2_tight hcarry1_fits (by omega)
  have hcarry2_fits : c21.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c21.val hc21_bound
  -- c31 = c3 + carry from c21
  have hc31_eq : c31.val = c3.val + c21.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  have hc31_bound : c31.val < 2 ^ 115 := by
    rw [hc31_eq]; exact carry_chain_lt_pow2_115 _ _ 23 hc3_tight hcarry2_fits (by omega)
  have hcarry3_fits : c31.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c31.val hc31_bound
  -- c41 = c4 + carry from c31
  have hc41_eq : c41.val = c4.val + c31.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  have hc41_bound : c41.val < 2 ^ 115 := by
    rw [hc41_eq]; exact carry_chain_lt_pow2_115 _ _ 5 hc4_tight hcarry3_fits (by omega)
  have hcarry4_fits : c41.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c41.val hc41_bound
  -- Array values after carry propagation
  -- Each ha'_i traces: a5[i] → chain of set operations → AND with mask → ci % 2^51
  have ha5_0 : a5[0]!.val = c0.val % 2 ^ 51 := by
    simp only [*, Array.set_of_ne_getElem! _ _ 0 4 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 0 3 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 0 2 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 0 1 (by agrind) (by agrind) (by omega),
      Array.set_of_eq _ _ 0 (by agrind), UScalar.val_and, UScalar.cast_val_eq,
      UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    omega
  have ha5_1 : a5[1]!.val = c11.val % 2 ^ 51 := by
    simp only [*, Array.set_of_ne_getElem! _ _ 1 4 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 1 3 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 1 2 (by agrind) (by agrind) (by omega),
      Array.set_of_eq _ _ 1 (by agrind),
      UScalar.val_and, UScalar.cast_val_eq, UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    omega
  have ha5_2 : a5[2]!.val = c21.val % 2 ^ 51 := by
    simp only [*, Array.set_of_ne_getElem! _ _ 2 4 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 2 3 (by agrind) (by agrind) (by omega),
      Array.set_of_eq _ _ 2 (by agrind), UScalar.val_and, UScalar.cast_val_eq, UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    omega
  have ha5_3 : a5[3]!.val = c31.val % 2 ^ 51 := by
    simp only [*, Array.set_of_ne_getElem! _ _ 3 4 (by agrind) (by agrind) (by omega),
      Array.set_of_eq _ _ 3 (by agrind), UScalar.val_and, UScalar.cast_val_eq,
      UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    omega
  have ha5_4 : a5[4]!.val = c41.val % 2 ^ 51 := by
    simp only [*, Array.set_of_eq _ _ 4 (by agrind), UScalar.val_and, UScalar.cast_val_eq,
      UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    agrind
  have hcarry_val : carry.val = c41.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  exact ⟨ha5_0,
    by rw [ha5_1, hc11_eq],
    by rw [ha5_2, hc21_eq, hc11_eq],
    by rw [ha5_3, hc31_eq, hc21_eq, hc11_eq],
    by rw [ha5_4, hc41_eq, hc31_eq, hc21_eq, hc11_eq],
    by rw [hcarry_val, hc41_eq, hc31_eq, hc21_eq, hc11_eq],
    by simp [*],
    by rw [hcarry_val]
       -- carry = c41/2^51 where c41 < 2^115
       -- c41 = c4 + c31/2^51 < 5*2^108 + 2^64 < 6*2^108
       -- carry = c41/2^51 < 6*2^108/2^51 = 6*2^57
       have : c41.val < 2 ^ 115 := hc41_bound
       have : c41.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 _ hc41_bound
       -- Tighter: c4 < 5*2^108, carry_from_c3 < 2^64
       -- c41 = c4 + carry_from_c3 < 5*2^108 + 2^64 < 6*2^108
       have hc41_tight : c41.val < 6 * 2 ^ 108 := by
         rw [hc41_eq]; omega
       have : (6 : ℕ) * 2 ^ 108 / 2 ^ 51 = 6 * 2 ^ 57 := by decide
       calc c41.val / 2 ^ 51 ≤ (6 * 2 ^ 108 - 1) / 2 ^ 51 := Nat.div_le_div_right (by omega)
         _ < 6 * 2 ^ 57 := by decide⟩

set_option maxHeartbeats 8000000 in
-- Required for step* through ~30 monadic operations
@[step]
theorem final_reduce_stage_spec (a' : Array U64 5#usize) (carry i34 : U64)
    (ha' : ∀ i < 5, a'[i]!.val < 2 ^ 51) (hcarry : carry.val < 6 * 2 ^ 57)
    (hmask : i34.val = 2 ^ 51 - 1) :
    final_reduce_stage a' carry i34 ⦃ (result : Array U64 5#usize) =>
      result[0]!.val = (a'[0]!.val + 19 * carry.val) % 2 ^ 51 ∧
      result[1]!.val = a'[1]!.val + (a'[0]!.val + 19 * carry.val) / 2 ^ 51 ∧
      result[2]!.val = a'[2]!.val ∧
      result[3]!.val = a'[3]!.val ∧
      result[4]!.val = a'[4]!.val ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold final_reduce_stage
  let* ⟨ i54, i54_post ⟩ ← U64.mul_spec
  let* ⟨ i55, i55_post ⟩ ← Array.index_usize_spec
  let* ⟨ i56, i56_post ⟩ ← U64.add_spec
  let* ⟨ a6, a6_post ⟩ ← Array.update_spec
  let* ⟨ i57, i57_post ⟩ ← Array.index_usize_spec
  let* ⟨ i58, i58_post1, i58_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i59, i59_post ⟩ ← Array.index_usize_spec
  -- Establish key facts before the add_spec (needed for overflow)
  have h_i55 : i55.val = a'[0]!.val := by simp [*]
  have h_i56 : i56.val = a'[0]!.val + 19 * carry.val := by
    simp only [i56_post, h_i55, i54_post]; omega
  have h_i57 : i57.val = a'[0]!.val + 19 * carry.val := by
    simp [*]; omega
  have h_i58 : i58.val = (a'[0]!.val + 19 * carry.val) / 2 ^ 51 := by
    simp only [i58_post1, Nat.shiftRight_eq_div_pow, h_i57]
  have h_i59 : i59.val = a'[1]!.val := by
    simp [*]
  let* ⟨ i60, i60_post ⟩ ← U64.add_spec
  let* ⟨ a7, a7_post ⟩ ← Array.update_spec
  let* ⟨ i61, i61_post ⟩ ← Array.index_usize_spec
  let* ⟨ i62, i62_post1, i62_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a8, a8_post ⟩ ← Array.update_spec
  -- Array values after final reduction
  -- a7[0]! = a6[0]! = i56 = a'[0]! + 19 * carry
  have ha7_0 : a7[0]!.val = a'[0]!.val + 19 * carry.val := by
    simp [a7_post, Array.set_of_ne_getElem! _ _ 0 1 (by agrind) (by agrind) (by omega),
      a6_post, h_i56]
  have ha8_0 : a8[0]!.val = (a'[0]!.val + 19 * carry.val) % 2 ^ 51 := by
    simp only [a8_post, Array.set_of_eq _ _ 0 (by agrind)]
    simp only [i62_post1, UScalar.val_and, hmask]
    rw [show i61 = a7[0]! from by simp [i61_post]]
    rw [Nat.and_two_pow_sub_one_eq_mod, ha7_0]
  have ha8_1 : a8[1]!.val = a'[1]!.val + (a'[0]!.val + 19 * carry.val) / 2 ^ 51 := by
    simp only [a8_post, Array.set_of_ne_getElem! _ _ 1 0 (by agrind) (by agrind) (by omega),
      a7_post, Array.set_of_eq _ _ 1 (by agrind),
      i60_post, h_i59, h_i58]
  have ha8_2 : a8[2]!.val = a'[2]!.val := by
    simp only [a8_post,
      a7_post, Array.set_of_ne_getElem! _ _ 2 1 (by agrind) (by agrind) (by omega),
      a6_post, Array.set_of_ne_getElem! _ _ 2 0 (by agrind) (by agrind) (by omega)]
  have ha8_3 : a8[3]!.val = a'[3]!.val := by
    simp only [a8_post,
      a7_post, Array.set_of_ne_getElem! _ _ 3 1 (by agrind) (by agrind) (by omega),
      a6_post, Array.set_of_ne_getElem! _ _ 3 0 (by agrind) (by agrind) (by omega)]
  have ha8_4 : a8[4]!.val = a'[4]!.val := by
    simp only [a8_post,
      a7_post, Array.set_of_ne_getElem! _ _ 4 1 (by agrind) (by agrind) (by omega),
      a6_post, Array.set_of_ne_getElem! _ _ 4 0 (by agrind) (by agrind) (by omega)]
  -- Limb bounds: all < 2^52
  have ha8_lt : ∀ i < 5, a8[i]!.val < 2 ^ 52 := by
    intro i hi; interval_cases i
    · rw [ha8_0]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by omega)
    · rw [ha8_1]
      have : a'[1]!.val < 2 ^ 51 := ha' 1 (by simp)
      have : a'[0]!.val < 2 ^ 51 := ha' 0 (by simp)
      have : (a'[0]!.val + 19 * carry.val) / 2 ^ 51 ≤ 2 ^ 13 - 1 := by omega
      omega
    · rw [ha8_2]; exact Nat.lt_of_lt_of_le (ha' 2 (by simp)) (by omega)
    · rw [ha8_3]; exact Nat.lt_of_lt_of_le (ha' 3 (by simp)) (by omega)
    · rw [ha8_4]; exact Nat.lt_of_lt_of_le (ha' 4 (by simp)) (by omega)
  exact ⟨ha8_0, ha8_1, ha8_2, ha8_3, ha8_4, ha8_lt⟩

/-! ## Main Proof -/

set_option maxHeartbeats 14000000 in
-- Required for step* through fold-decomposed loop body
@[step]
theorem pow2k_loop_spec (k : U32) (a : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    pow2k_loop k a ⦃ (result : Std.Array U64 5#usize) =>
      Field51_as_Nat result ≡ (Field51_as_Nat a)^(2^k.val) [MOD p] ∧
      (if k.val = 0 then result = a else ∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold pow2k_loop
  split
  case isTrue hlt =>
    simp_rw [fold_square_stage, fold_carry_prop_stage, fold_final_reduce_stage]
    step as ⟨ sq, sq_post ⟩
    step as ⟨ cp, cp_post ⟩
    step as ⟨ red, red_post1, red_post2, red_post3, red_post4, red_post5, red_post6 ⟩
    · intro i hi; obtain ⟨h0, h1, h2, h3, h4, _⟩ := cp_post
      interval_cases i <;> simp only [*] <;> exact Nat.mod_lt _ (by positivity)
    step as ⟨ k1, k1_post1, k1_post2 ⟩
    step with pow2k_loop_spec as ⟨ result, result_post1, result_post2 ⟩
    -- Extract carry prop postconditions
    have ha'_0 := cp_post.1
    have ha'_1 := cp_post.2.1
    have ha'_2 := cp_post.2.2.1
    have ha'_3 := cp_post.2.2.2.1
    have ha'_4 := cp_post.2.2.2.2.1
    have hcarry_val := cp_post.2.2.2.2.2.1
    -- Squaring identity mod p
    have a_pow_two : (sq.1.val + 2^51 * sq.2.1.val + 2^102 * sq.2.2.1.val +
        2^153 * sq.2.2.2.1.val + 2^204 * sq.2.2.2.2.val)
        ≡ (Field51_as_Nat a)^2 [MOD p] := by
      have := decompose a[0]!.val a[1]!.val a[2]!.val a[3]!.val a[4]!.val
      have := sq_post.1; have := sq_post.2.1; have := sq_post.2.2.1
      have := sq_post.2.2.2.1; have := sq_post.2.2.2.2.1
      simp_all only [Nat.ModEq, Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, mul_zero, pow_zero, one_mul]
    -- Carry chain conservation
    have h_chain := carry_chain_eq sq.1.val sq.2.1.val sq.2.2.1.val sq.2.2.2.1.val sq.2.2.2.2.val
        _ _ _ _ _ _
        (sq.2.1.val + sq.1.val / 2^51)
        (sq.2.2.1.val + (sq.2.1.val + sq.1.val / 2^51) / 2^51)
        (sq.2.2.2.1.val + (sq.2.2.1.val + (sq.2.1.val + sq.1.val / 2^51) / 2^51) / 2^51)
        (sq.2.2.2.2.val + (sq.2.2.2.1.val + (sq.2.2.1.val + (sq.2.1.val + sq.1.val / 2^51) / 2^51) / 2^51) / 2^51)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    -- Field51_as_Nat of the reduced result
    have hf_r : Field51_as_Nat red =
        (cp.1[0]!.val + 19 * cp.2.1.val) + 2^51 * cp.1[1]!.val + 2^102 * cp.1[2]!.val +
        2^153 * cp.1[3]!.val + 2^204 * cp.1[4]!.val := by
      unfold Field51_as_Nat
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      rw [red_post1, red_post2, red_post3, red_post4, red_post5]
      have := Nat.mod_add_div (cp.1[0]!.val + 19 * cp.2.1.val) (2 ^ 51)
      omega
    -- h_key: Field51_as_Nat red + carry * p = c0 + 2^51*c1 + ...
    have h_key : Field51_as_Nat red + cp.2.1.val * p =
        sq.1.val + 2^51 * sq.2.1.val + 2^102 * sq.2.2.1.val +
        2^153 * sq.2.2.2.1.val + 2^204 * sq.2.2.2.2.val := by
      rw [hf_r, h_chain]
      simp only [ha'_0, ha'_1, ha'_2, ha'_3, ha'_4, hcarry_val]
      unfold p; omega
    have hsq : Field51_as_Nat red ≡ (Field51_as_Nat a)^2 [MOD p] :=
      (modeq_of_add_mul_eq _ _ cp.2.1.val p h_key).trans a_pow_two
    have hpow := Nat.ModEq.pow (2^k1.val) hsq
    constructor
    · apply Nat.ModEq.trans result_post1 hpow |>.trans
      rw [← pow_mul]
      have hk_pos : k.val ≥ 1 := by omega
      have : k1.val = k.val - 1 := by agrind
      rw [this]
      have h2k : 2 * 2 ^ (k.val - 1) = 2 ^ k.val := by
        conv_rhs => rw [← Nat.sub_add_cancel hk_pos, Nat.pow_succ']
      rw [h2k]
    · simp only [show k.val ≠ 0 by omega]
      by_cases hk1 : k1.val = 0
      · simp only [hk1] at result_post2
        rw [result_post2]; exact red_post6
      · simp only [hk1, ite_false] at result_post2
        exact result_post2
  case isFalse hge =>
    step*
    have : k.val = 0 := by agrind
    simpa [this] using Nat.ModEq.trans rfl rfl
  termination_by k.val
  decreasing_by agrind

@[step]
theorem pow2k_spec (self : Array U64 5#usize) (k : U32) (_ : 0 < k.val)
    (_ : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow2k self k ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (Field51_as_Nat self)^(2^k.val) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold pow2k
  step*
  exact ⟨‹_›, by agrind⟩

end curve25519_dalek.backend.serial.u64.field.FieldElement51.v3
