/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Mathlib.Data.Nat.ModEq

/-! # Spec Theorem for `FieldElement51::sub`

Specification and proof for `FieldElement51::sub`.

This function performs field element subtraction. To avoid underflow, a multiple
of p is added.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51
open backend.serial.u64.field

/-
natural language description:

    • Takes two input FieldElement51s a and b and returns another FieldElement51 d
      that is a representant of the difference a - b in the field (modulo p = 2^255 - 19).

    • The implementation adds a multiple of p (namely 16p) as a bias value to a before
      subtraction is performed to avoid underflow: computes (a + 16*p) - b, then reduces

natural language specs:

    • For appropriately bounded FieldElement51s a and b:
      Field51_as_Nat(sub(a, b)) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p), or equivalently
      Field51_as_Nat(sub(a, b)) + Field51_as_Nat(b) ≡ Field51_as_Nat(a) (mod p)
-/

set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.sub`**:
- No panic (always returns successfully when bounds are satisfied)
- The result d satisfies the field subtraction property:

  Field51_as_Nat(d) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p), or equivalently
  Field51_as_Nat(d) + Field51_as_Nat(b) ≡ Field51_as_Nat(a) (mod p)

- Requires that input limbs are bounded:
  - For a: limbs must allow addition with 16*p without U64 overflow
    - a[0] must be ≤ 18410715276690587951 (= 2^64 - 1 - 36028797018963664)
    - a[1..4] must be ≤ 18410715276690587663 (= 2^64 - 1 - 36028797018963952)
  - For b: limbs must be ≤ the constants (representing 16*p) to avoid underflow
    - b[0] must be ≤ 36028797018963664
    - b[1..4] must be ≤ 36028797018963952
  To make the theorem more easily readable and provable, we
  replace these precise bounds with the slightly looser bounds
  a[i] < 2^63  and b[i] < 2^54
-/
@[progress]
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 63) (hb : ∀ i < 5, b[i]!.val < 2 ^ 54) :
    sub a b ⦃ (d : FieldElement51) =>
      (∀ i < 5, d[i]!.val < 2 ^ 52) ∧
      (Field51_as_Nat d + Field51_as_Nat b) % p = Field51_as_Nat a % p ⦄ := by
  unfold sub
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
  let* ⟨ i1, i1_post ⟩ ← U64.add_spec
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
  let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U64.sub_spec
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
  let* ⟨ i5, i5_post ⟩ ← U64.add_spec
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
  let* ⟨ i7, i7_post_1, i7_post_2 ⟩ ← U64.sub_spec
  let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
  let* ⟨ i9, i9_post ⟩ ← U64.add_spec
  let* ⟨ i10, i10_post ⟩ ← Array.index_usize_spec
  let* ⟨ i11, i11_post_1, i11_post_2 ⟩ ← U64.sub_spec
  let* ⟨ i12, i12_post ⟩ ← Array.index_usize_spec
  let* ⟨ i13, i13_post ⟩ ← U64.add_spec
  let* ⟨ i14, i14_post ⟩ ← Array.index_usize_spec
  let* ⟨ i15, i15_post_1, i15_post_2 ⟩ ← U64.sub_spec
  let* ⟨ i16, i16_post ⟩ ← Array.index_usize_spec
  let* ⟨ i17, i17_post ⟩ ← U64.add_spec
  let* ⟨ i18, i18_post ⟩ ← Array.index_usize_spec
  let* ⟨ i19, i19_post_1, i19_post_2 ⟩ ← U64.sub_spec
  let* ⟨ res, res_post_1, res_post_2 ⟩ ← reduce_spec
  refine ⟨by assumption, ?_⟩
  -- modular arithmetic property
  have htmp : Field51_as_Nat res + Field51_as_Nat b ≡
    Field51_as_Nat (Array.make 5#usize [i3, i7, i11, i15, i19]) + Field51_as_Nat b [MOD p] := by
    apply Nat.ModEq.add_right; apply Nat.ModEq.symm; assumption
  apply Nat.ModEq.trans htmp
  unfold Field51_as_Nat
  simp only [← Finset.sum_add_distrib, ← Nat.mul_add]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Array.make, Array.getElem!_Nat_eq, Nat.reduceMul,
             show ([i3, i7, i11, i15, i19] : List U64)[0]! = i3 from rfl,
             show ([i3, i7, i11, i15, i19] : List U64)[1]! = i7 from rfl,
             show ([i3, i7, i11, i15, i19] : List U64)[2]! = i11 from rfl,
             show ([i3, i7, i11, i15, i19] : List U64)[3]! = i15 from rfl,
             show ([i3, i7, i11, i15, i19] : List U64)[4]! = i19 from rfl]
  have h0 : i3.val + b[0]!.val = a[0]!.val + 36028797018963664 := by grind
  have h1 : i7.val + b[1]!.val = a[1]!.val + 36028797018963952 := by grind
  have h2 : i11.val + b[2]!.val = a[2]!.val + 36028797018963952 := by grind
  have h3 : i15.val + b[3]!.val = a[3]!.val + 36028797018963952 := by grind
  have h4 : i19.val + b[4]!.val = a[4]!.val + 36028797018963952 := by grind
  -- Normalize Array.getElem! to List.getElem! in hypotheses to match goal
  simp only [Array.getElem!_Nat_eq] at h0 h1 h2 h3 h4
  rw [h0, h1, h2, h3, h4]
  -- Rearrange: ∑ 2^k*(a_k + c_k) = (∑ 2^k*a_k) + (∑ 2^k*c_k)
  have hrearr : ∀ (x0 x1 x2 x3 x4 : ℕ),
      2 ^ 0 * (x0 + 36028797018963664) + 2 ^ 51 * (x1 + 36028797018963952) +
      2 ^ 102 * (x2 + 36028797018963952) + 2 ^ 153 * (x3 + 36028797018963952) +
      2 ^ 204 * (x4 + 36028797018963952) =
      (2 ^ 0 * x0 + 2 ^ 51 * x1 + 2 ^ 102 * x2 + 2 ^ 153 * x3 + 2 ^ 204 * x4) +
      (2 ^ 0 * 36028797018963664 + 2 ^ 51 * 36028797018963952 +
       2 ^ 102 * 36028797018963952 + 2 ^ 153 * 36028797018963952 +
       2 ^ 204 * 36028797018963952) := by intro x0 x1 x2 x3 x4; ring
  conv_lhs => rw [hrearr]
  set kjsum := 2 ^ 0 * 36028797018963664 + 2 ^ 51 * 36028797018963952 +
               2 ^ 102 * 36028797018963952 + 2 ^ 153 * 36028797018963952 +
               2 ^ 204 * 36028797018963952
  have kmod0 : kjsum ≡ 0 [MOD p] := by
    rw [Nat.modEq_zero_iff_dvd, p]
    simp only [kjsum]
    decide
  set asum := 2 ^ 0 * (↑(↑a : List U64)[0]! : ℕ) + 2 ^ 51 * (↑(↑a : List U64)[1]! : ℕ) +
              2 ^ 102 * (↑(↑a : List U64)[2]! : ℕ) + 2 ^ 153 * (↑(↑a : List U64)[3]! : ℕ) +
              2 ^ 204 * (↑(↑a : List U64)[4]! : ℕ)
  have h := Nat.ModEq.add_left asum kmod0
  simp only [add_zero] at h
  exact h

end curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51
