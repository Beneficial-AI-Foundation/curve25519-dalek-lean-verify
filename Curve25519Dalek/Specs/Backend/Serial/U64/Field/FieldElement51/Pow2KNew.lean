/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/- # Spec Theorem for `FieldElement51::pow2k`

Specification and proof for `FieldElement51::pow2k`.

This function computes the 2^k-th power of the element.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

-/

set_option maxHeartbeats 5000000

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

@[progress]
theorem pow2k.m_spec (x y : U64) :
    ∃ prod : U128, pow2k.m x y = ok prod ∧
    prod.val = x.val * y.val := by
  unfold pow2k.m
  progress*
  suffices x.val * y.val < 2^64 * 2^64 by scalar_tac
  apply Nat.mul_lt_mul''
  · scalar_tac
  · scalar_tac

/-- Compute the 5 limbs of a² (before carry propagation) using radix-2^51 squaring.
    Uses the identity 2^255 ≡ 19 (mod p) to reduce overflow terms. -/
def compute_square_limbs (a : Array U64 5#usize) : Result (U128 × U128 × U128 × U128 × U128) := do
  let a0 := a[0]!
  let a1 := a[1]!
  let a2 := a[2]!
  let a3 := a[3]!
  let a4 := a[4]!
  let a3_19 ← 19#u64 * a3
  let a4_19 ← 19#u64 * a4
  -- c0 = a0² + 2*(a1*a4_19 + a2*a3_19)
  let t0 ← pow2k.m a0 a0
  let t1 ← pow2k.m a1 a4_19
  let t2 ← pow2k.m a2 a3_19
  let t3 ← t1 + t2
  let t4 ← 2#u128 * t3
  let c0 ← t0 + t4
  -- c1 = a3*a3_19 + 2*(a0*a1 + a2*a4_19)
  let t5 ← pow2k.m a3 a3_19
  let t6 ← pow2k.m a0 a1
  let t7 ← pow2k.m a2 a4_19
  let t8 ← t6 + t7
  let t9 ← 2#u128 * t8
  let c1 ← t5 + t9
  -- c2 = a1² + 2*(a0*a2 + a4*a3_19)
  let t10 ← pow2k.m a1 a1
  let t11 ← pow2k.m a0 a2
  let t12 ← pow2k.m a4 a3_19
  let t13 ← t11 + t12
  let t14 ← 2#u128 * t13
  let c2 ← t10 + t14
  -- c3 = a4*a4_19 + 2*(a0*a3 + a1*a2)
  let t15 ← pow2k.m a4 a4_19
  let t16 ← pow2k.m a0 a3
  let t17 ← pow2k.m a1 a2
  let t18 ← t16 + t17
  let t19 ← 2#u128 * t18
  let c3 ← t15 + t19
  -- c4 = a2² + 2*(a0*a4 + a1*a3)
  let t20 ← pow2k.m a2 a2
  let t21 ← pow2k.m a0 a4
  let t22 ← pow2k.m a1 a3
  let t23 ← t21 + t22
  let t24 ← 2#u128 * t23
  let c4 ← t20 + t24
  ok (c0, c1, c2, c3, c4)

/-- The square limbs represent a² in radix-2^51 form modulo p.
    c0 + 2^51*c1 + 2^102*c2 + 2^153*c3 + 2^204*c4 ≡ (Field51_as_Nat a)² [MOD p] -/
@[progress]
theorem compute_square_limbs_spec (a : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    ∃ c0 c1 c2 c3 c4 : U128, compute_square_limbs a = ok (c0, c1, c2, c3, c4) ∧
    (c0.val + 2^51 * c1.val + 2^102 * c2.val + 2^153 * c3.val + 2^204 * c4.val)
      ≡ (Field51_as_Nat a)^2 [MOD p] := by
  unfold compute_square_limbs
  progress*
  · have := ha 3 (by simp)
    scalar_tac
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry

@[progress]
theorem pow2k_loop_spec (k : ℕ) (k' : U32) (a : Array U64 5#usize)
    (hk : 0 < k) (eqk : k'.val = k)
    (h_bounds : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    ∃ r, pow2k_loop k' a = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) := by
  unfold pow2k_loop
  progress*
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

@[progress]
theorem pow2k_spec (self : Array U64 5#usize) (k : U32) (hk : 0 < k.val)
    (ha : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    ∃ result : FieldElement51, pow2k self k = ok result ∧
    Field51_as_Nat result ≡ (Field51_as_Nat self)^(2^k.val) [MOD p] ∧
    (∀ i < 5, result[i]!.val < 2 ^ 52) := by
  unfold pow2k
  progress*
  grind

end curve25519_dalek.backend.serial.u64.field.FieldElement51
