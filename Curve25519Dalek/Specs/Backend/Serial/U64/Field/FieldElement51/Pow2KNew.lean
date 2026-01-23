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

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

theorem pow2k.m_spec (x y : U64) :
    ∃ prod : U128, pow2k.m x y = ok prod ∧
    prod.val = x.val * y.val := by
  unfold pow2k.m
  progress*
  suffices x.val * y.val < 2^64 * 2^64 by scalar_tac
  apply Nat.mul_lt_mul''
  · scalar_tac
  · scalar_tac

theorem pow2k_loop_spec (k : ℕ) (k' : U32) (a : Array U64 5#usize)
    (hk : 0 < k) (eqk : k'.val = k)
    (h_bounds : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    ∃ r, pow2k_loop k' a = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) := by
  sorry

theorem pow2k_spec (self : Array U64 5#usize) (k : U32) (hk : 0 < k.val)
    (ha : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    ∃ result : FieldElement51, pow2k self k = ok result ∧
    Field51_as_Nat result ≡ (Field51_as_Nat self)^(2^k.val) [MOD p] ∧
    (∀ i < 5, result[i]!.val < 2 ^ 52) := by
  unfold pow2k

  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
