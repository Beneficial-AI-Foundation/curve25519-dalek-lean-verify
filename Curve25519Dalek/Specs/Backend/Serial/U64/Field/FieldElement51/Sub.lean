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
    (h_bounds_a : ∀ i < 5, a[i]!.val < 2 ^ 63)
    (h_bounds_b : ∀ i < 5, b[i]!.val < 2 ^ 54) :
    sub a b ⦃ d =>
    (∀ i < 5, d[i]!.val < 2 ^ 52) ∧
    (Field51_as_Nat d + Field51_as_Nat b) % p = Field51_as_Nat a % p ⦄ := by
  unfold sub
  progress as ⟨i0, hi0⟩    -- a[0]
  progress as ⟨i1, hi1⟩    -- a[0] + k
  · have := h_bounds_a 0 (by simp); scalar_tac
  progress as ⟨i2, hi2⟩    -- b[0]
  progress as ⟨i3, hi3⟩    -- (a[0]+k) - b[0]
  · have := h_bounds_b 0 (by simp); scalar_tac
  progress as ⟨i4, hi4⟩    -- a[1]
  progress as ⟨i5, hi5⟩    -- a[1] + j
  · have := h_bounds_a 1 (by simp); scalar_tac
  progress as ⟨i6, hi6⟩    -- b[1]
  progress as ⟨i7, hi7⟩    -- (a[1]+j) - b[1]
  · have := h_bounds_b 1 (by simp); scalar_tac
  progress as ⟨i8, hi8⟩    -- a[2]
  progress as ⟨i9, hi9⟩    -- a[2] + j
  · have := h_bounds_a 2 (by simp); scalar_tac
  progress as ⟨i10, hi10⟩  -- b[2]
  progress as ⟨i11, hi11⟩  -- (a[2]+j) - b[2]
  · have := h_bounds_b 2 (by simp); scalar_tac
  progress as ⟨i12, hi12⟩  -- a[3]
  progress as ⟨i13, hi13⟩  -- a[3] + j
  · have := h_bounds_a 3 (by simp); scalar_tac
  progress as ⟨i14, hi14⟩  -- b[3]
  progress as ⟨i15, hi15⟩  -- (a[3]+j) - b[3]
  · have := h_bounds_b 3 (by simp); scalar_tac
  progress as ⟨i16, hi16⟩  -- a[4]
  progress as ⟨i17, hi17⟩  -- a[4] + j
  · have := h_bounds_a 4 (by simp); scalar_tac
  progress as ⟨i18, hi18⟩  -- b[4]
  progress as ⟨i19, hi19⟩  -- (a[4]+j) - b[4]
  · have := h_bounds_b 4 (by simp); scalar_tac
  progress as ⟨res, hres_bounds, hres_mod⟩  -- reduce
  refine ⟨fun i hi => by have := hres_bounds i hi; omega, ?_⟩
  -- modular arithmetic property
  have htmp : Field51_as_Nat res + Field51_as_Nat b ≡
    Field51_as_Nat (Array.make 5#usize [i3, i7, i11, i15, i19]) + Field51_as_Nat b [MOD p] := by
    apply Nat.ModEq.add_right; apply Nat.ModEq.symm; exact hres_mod
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
  have h0 : i3.val + b[0]!.val = a[0]!.val + 36028797018963664 := by scalar_tac
  have h1 : i7.val + b[1]!.val = a[1]!.val + 36028797018963952 := by scalar_tac
  have h2 : i11.val + b[2]!.val = a[2]!.val + 36028797018963952 := by scalar_tac
  have h3 : i15.val + b[3]!.val = a[3]!.val + 36028797018963952 := by scalar_tac
  have h4 : i19.val + b[4]!.val = a[4]!.val + 36028797018963952 := by scalar_tac
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
    native_decide
  set asum := 2 ^ 0 * (↑(↑a : List U64)[0]! : ℕ) + 2 ^ 51 * (↑(↑a : List U64)[1]! : ℕ) +
              2 ^ 102 * (↑(↑a : List U64)[2]! : ℕ) + 2 ^ 153 * (↑(↑a : List U64)[3]! : ℕ) +
              2 ^ 204 * (↑(↑a : List U64)[4]! : ℕ)
  have h := Nat.ModEq.add_left asum kmod0
  simp only [add_zero] at h
  exact h
  /- OLD PROOF (needs updating for WP spec form):
  unfold sub
  -- To do: some problem using `progress*` in this proof and so doing each step manually.
  -- Change to `progress*` when possible.

  set k := 36028797018963664#u64 with hk
  set j := 36028797018963952#u64 with hj

  -- Limb 0
  have hlen_a0 : 0#usize < a.length := by scalar_tac
  obtain ⟨a0, ha0_ok⟩ := Array.index_usize_spec a 0#usize hlen_a0
  simp only [ha0_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha0 : (a.val)[0]! = a0

  have ha0_bound : a0.val + k.val ≤ U64.max := by
    have := h_bounds_a 0 (by simp); scalar_tac
  obtain ⟨a0', ha0'_ok, ha0'_val⟩ := U64.add_spec ha0_bound
  simp only [ha0'_ok, bind_tc_ok]

  have hlen_b0 : 0#usize < b.length := by scalar_tac
  obtain ⟨b0, hb0_ok⟩ := Array.index_usize_spec b 0#usize hlen_b0
  simp only [hb0_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb0 : (b.val)[0]! = b0

  have ha0'_sub_bound : b0 ≤ a0'.val := by
    rw [ha0'_val, ← hb0]
    have := h_bounds_b 0 (by simp); scalar_tac
  obtain ⟨i3, hi3_ok, hi3_val, hi3_val'⟩ := U64.sub_spec ha0'_sub_bound
  simp only [hi3_ok, bind_tc_ok]

  -- Limb 1
  have hlen_a1 : 1#usize < a.length := by scalar_tac
  obtain ⟨a1, ha1_ok⟩ := Array.index_usize_spec a 1#usize hlen_a1
  simp only [ha1_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha1 : (a.val)[1]! = a1

  have ha1_bound : a1.val + j.val ≤ U64.max := by
    have := h_bounds_a 1 (by simp); scalar_tac
  obtain ⟨a1', ha1'_ok, ha1'_val⟩ := U64.add_spec ha1_bound
  simp only [ha1'_ok, bind_tc_ok]

  have hlen_b1 : 1#usize < b.length := by scalar_tac
  obtain ⟨b1, hb1_ok⟩ := Array.index_usize_spec b 1#usize hlen_b1
  simp only [hb1_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb1 : (b.val)[1]! = b1

  have ha1'_sub_bound : b1 ≤ a1'.val := by
    rw [ha1'_val, ← hb1]
    have := h_bounds_b 1 (by simp); scalar_tac
  obtain ⟨i7, hi7_ok, hi7_val, hi7_val'⟩ := U64.sub_spec ha1'_sub_bound
  simp only [hi7_ok, bind_tc_ok]

  -- Limb 2
  have hlen_a2 : 2#usize < a.length := by scalar_tac
  obtain ⟨a2, ha2_ok⟩ := Array.index_usize_spec a 2#usize hlen_a2
  simp only [ha2_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha2 : (a.val)[2]! = a2

  have ha2_bound : a2.val + j.val ≤ U64.max := by
    have := h_bounds_a 2 (by simp); scalar_tac
  obtain ⟨a2', ha2'_ok, ha2'_val⟩ := U64.add_spec ha2_bound
  simp only [ha2'_ok, bind_tc_ok]

  have hlen_b2 : 2#usize < b.length := by scalar_tac
  obtain ⟨b2, hb2_ok⟩ := Array.index_usize_spec b 2#usize hlen_b2
  simp only [hb2_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb2 : (b.val)[2]! = b2

  have ha2'_sub_bound : b2 ≤ a2'.val := by
    rw [ha2'_val, ← hb2]
    have := h_bounds_b 2 (by simp); scalar_tac
  obtain ⟨i11, hi11_ok, hi11_val, hi11_val'⟩ := U64.sub_spec ha2'_sub_bound
  simp only [hi11_ok, bind_tc_ok]

  -- Limb 3
  have hlen_a3 : 3#usize < a.length := by scalar_tac
  obtain ⟨a3, ha3_ok⟩ := Array.index_usize_spec a 3#usize hlen_a3
  simp only [ha3_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha3 : (a.val)[3]! = a3

  have ha3_bound : a3.val + j.val ≤ U64.max := by
    have := h_bounds_a 3 (by simp); scalar_tac
  obtain ⟨a3', ha3'_ok, ha3'_val⟩ := U64.add_spec ha3_bound
  simp only [ha3'_ok, bind_tc_ok]

  have hlen_b3 : 3#usize < b.length := by scalar_tac
  obtain ⟨b3, hb3_ok⟩ := Array.index_usize_spec b 3#usize hlen_b3
  simp only [hb3_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb3 : (b.val)[3]! = b3

  have ha3'_sub_bound : b3 ≤ a3'.val := by
    rw [ha3'_val, ← hb3]
    have := h_bounds_b 3 (by simp); scalar_tac
  obtain ⟨i15, hi15_ok, hi15_val, hi15_val'⟩ := U64.sub_spec ha3'_sub_bound
  simp only [hi15_ok, bind_tc_ok]

  -- Limb 4
  have hlen_a4 : 4#usize < a.length := by scalar_tac
  obtain ⟨a4, ha4_ok⟩ := Array.index_usize_spec a 4#usize hlen_a4
  simp only [ha4_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize ha4 : (a.val)[4]! = a4

  have ha4_bound : a4.val + j.val ≤ U64.max := by
    have := h_bounds_a 4 (by simp); scalar_tac
  obtain ⟨a4', ha4'_ok, ha4'_val⟩ := U64.add_spec ha4_bound
  simp only [ha4'_ok, bind_tc_ok]

  have hlen_b4 : 4#usize < b.length := by scalar_tac
  obtain ⟨b4, hb4_ok⟩ := Array.index_usize_spec b 4#usize hlen_b4
  simp only [hb4_ok, bind_tc_ok, UScalar.ofNat_val_eq]
  generalize hb4 : (b.val)[4]! = b4

  have ha4'_sub_bound : b4 ≤ a4'.val := by
    rw [ha4'_val, ← hb4]
    have := h_bounds_b 4 (by simp); scalar_tac
  obtain ⟨i19, hi19_ok, hi19_val, hi19_val'⟩ := U64.sub_spec ha4'_sub_bound
  simp only [hi19_ok, bind_tc_ok]

  -- Call reduce and get the result
  obtain ⟨d, hreduce_ok, hreduce_bounds, hreduce_eq⟩ :=
    reduce_spec (Array.make 5#usize [i3, i7, i11, i15, i19])
  simp only [hreduce_ok, ok.injEq, exists_eq_left']

  refine ⟨fun i hi ↦ ?_, ?_⟩
  · grind
  · -- Prove the modular arithmetic property
    have htmp : Field51_as_Nat d + Field51_as_Nat b ≡
      Field51_as_Nat (Array.make 5#usize [i3, i7, i11, i15, i19]) + Field51_as_Nat b [MOD p] := by
      apply Nat.ModEq.add_right; apply Nat.ModEq.symm; exact hreduce_eq
    apply Nat.ModEq.trans htmp
    unfold Field51_as_Nat
    simp only [← Finset.sum_add_distrib, ← Nat.mul_add]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one]
    have id0 : (Array.make 5#usize [i3, i7, i11, i15, i19])[0]! = i3 := by rfl
    have id1 : (Array.make 5#usize [i3, i7, i11, i15, i19])[1]! = i7 := by rfl
    have id2 : (Array.make 5#usize [i3, i7, i11, i15, i19])[2]! = i11 := by rfl
    have id3 : (Array.make 5#usize [i3, i7, i11, i15, i19])[3]! = i15 := by rfl
    have id4 : (Array.make 5#usize [i3, i7, i11, i15, i19])[4]! = i19 := by rfl
    rw [id0, id1, id2, id3, id4]
    have eq01 :
      (i3.val + b[0]! = i3.val + b0) ∧
      (i7.val + b[1]! = i7.val + b1) ∧
      (i11.val + b[2]! = i11.val + b2) ∧
      (i15.val + b[3]! = i15.val + b3) ∧
      (i19.val + b[4]! = i19.val + b4) := by
      rw [← hb0, ← hb1, ← hb2, ← hb3, ← hb4]; scalar_tac
    rw [eq01.left, eq01.right.left, eq01.right.right.left, eq01.right.right.right.left, eq01.right.right.right.right]
    have eq0 : i3.val + b0 = a0' := by
      rw [hi3_val]; apply Nat.sub_add_cancel; exact hi3_val'
    have eq1 : i7.val + b1 = a1' := by
      rw [hi7_val]; apply Nat.sub_add_cancel; exact hi7_val'
    have eq2 : i11.val + b2 = a2' := by
      rw [hi11_val]; apply Nat.sub_add_cancel; exact hi11_val'
    have eq3 : i15.val + b3 = a3' := by
      rw [hi15_val]; apply Nat.sub_add_cancel; exact hi15_val'
    have eq4 : i19.val + b4 = a4' := by
      rw [hi19_val]; apply Nat.sub_add_cancel; exact hi19_val'
    rw [eq0, eq1, eq2, eq3, eq4, ha0'_val, ha1'_val, ha2'_val, ha3'_val, ha4'_val]
    have eqsum :
      2 ^ (51 * 0) * (a0.val + k.val) +
      2 ^ (51 * 1) * (a1.val + j.val) +
      2 ^ (51 * 2) * (a2.val + j.val) +
      2 ^ (51 * 3) * (a3.val + j.val) +
      2 ^ (51 * 4) * (a4.val + j.val)
      =
      (2 ^ (51 * 0) * a0.val + 2 ^ (51 * 1) * a1.val + 2 ^ (51 * 2) * a2.val + 2 ^ (51 * 3) * a3.val + 2 ^ (51 * 4) * a4.val) +
      (2 ^ (51 * 0) * k.val + 2 ^ (51 * 1) * j.val + 2 ^ (51 * 2) * j.val + 2 ^ (51 * 3) * j.val + 2 ^ (51 * 4) * j.val) := by
      repeat (rw [Nat.mul_add])
      ring
    rw [eqsum]
    set asum := 2 ^ (51 * 0) * a0.val + 2 ^ (51 * 1) * a1.val + 2 ^ (51 * 2) * a2.val + 2 ^ (51 * 3) * a3.val + 2 ^ (51 * 4) * a4.val with hasum
    set kjsum := 2 ^ (51 * 0) * k.val + 2 ^ (51 * 1) * j.val + 2 ^ (51 * 2) * j.val + 2 ^ (51 * 3) * j.val + 2 ^ (51 * 4) * j.val with hkjsum
    have hsumeq : asum = 2 ^ (51 * 0) * ↑a[0]! + 2 ^ (51 * 1) * ↑a[1]! + 2 ^ (51 * 2) * ↑a[2]! + 2 ^ (51 * 3) * ↑a[3]! + 2 ^ (51 * 4) * ↑a[4]! := by
      rw [hasum, ← ha0, ← ha1, ← ha2, ← ha3, ← ha4]; scalar_tac
    rw [← hsumeq]
    have kmod0 : kjsum ≡ 0 [MOD p] := by
      rw [Nat.modEq_zero_iff_dvd]
      rw [hkjsum, hk, hj, p]
      simp
    have final := Nat.ModEq.add_left asum kmod0
    simp only [add_zero] at final
    exact final
  -/

end curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51
