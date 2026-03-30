/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux


/-! # Spec Theorems for `read_le_u64_into`

Specification and proof for `read_le_u64_into` (lines 1376:0–1393:1) and its
loop auxiliary `read_le_u64_into_loop` (lines 1379:4–1392:5).


In each iteration `i` (from `0` to `dst.len() − 1`) the loop body:
1. Computes the byte offset `start = 8 * i`.
2. Reads the 8 consecutive bytes `src[8i], src[8i+1], …, src[8i+7]`.
3. Assembles them as a **little-endian** `u64`:
      `dst[i] ← src[8i] + 2^8 · src[8i+1] + … + 2^56 · src[8i+7]`.

## Loop invariant

At loop counter `i` (with `i ≤ dst.len = n`), the slice `dst` satisfies:

  **Element correctness** — for all `k < i`:
    `dst[k].val = ∑ j ∈ Finset.range 8, src.val[8k+j].val · 2^(8j)`
               `= U8Slice_chunk_as_U64 src k`.

Each iteration extends this invariant from `i` to `i + 1` by:
- Reading `src.val[8i], …, src.val[8i+7]` via `Slice.index_usize`.
- Computing their little-endian `u64` value via `core.num.U64.from_le_bytes`.
- Writing the result to `dst` position `i` via `Slice.update`.

## Postconditions

After `read_le_u64_into src dst` (with `src.len = 8 * n`, `n = dst.len`):
1. **Element correctness**: `∀ k < n, result[k].val = U8Slice_chunk_as_U64 src k`.
2. **Combined-value preservation**:
     `U64Slice_as_Nat result n = ∑ j ∈ Finset.range (8*n), src.val[j].val · 2^(8j)`.

The combined-value property is the key fact consumed by callers.  When
`n = 4` and `src` comes from a 32-byte `Scalar`, this reads:
  `X64_as_Nat (index_mut_back result) = U8x32_as_Nat self.bytes`
where `X64_as_Nat` is the 4-limb `u64` interpretation from `AsRadix2wLoop.lean`.

**Source**: curve25519-dalek/src/scalar.rs, lines 1376:0-1393:1
-/

set_option linter.hashCommand false
#setup_aeneas_simps
attribute [-simp] Int.reducePow Nat.reducePow

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.scalar


/-
natural language specs:

• The function always succeeds whenever `src.len = 8 * dst.len`.
• On return, for every `k < n`:
    `result[k].val = src.val[8k+0].val · 2^0  +  src.val[8k+1].val · 2^8
                   + src.val[8k+2].val · 2^16 +  src.val[8k+3].val · 2^24
                   + src.val[8k+4].val · 2^32 +  src.val[8k+5].val · 2^40
                   + src.val[8k+6].val · 2^48 +  src.val[8k+7].val · 2^56`
  which is the little-endian `u64` interpretation of the `k`-th 8-byte chunk.
• Equivalently, the combined value is preserved:
    `∑ k < n, result[k].val · 2^(64k) = ∑ j < 8n, src.val[j].val · 2^(8j)`.
-/

/-- Interpret 8 consecutive bytes of slice `src` beginning at byte offset `8 * k`
    as a natural number in **little-endian** byte order:
    `∑ j ∈ Finset.range 8, src.val[8k+j].val · 2^(8j)`.

    This is the natural-number value that `u64::from_le_bytes` returns for the
    8-byte chunk `[src[8k], src[8k+1], …, src[8k+7]]`. -/
def U8Slice_chunk_as_U64 (src : Slice Std.U8) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range 8, (src.val[8 * k + j]!).val * 2 ^ (8 * j)

def U64Slice_as_Nat (dst : Slice Std.U64) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (dst.val[k]!).val * 2 ^ (64 * k)

private lemma chunk_step_identity (src : Slice Std.U8) (k : ℕ) :
    ∑ j ∈ Finset.range (8 * (k + 1)), (src.val[j]!).val * 2 ^ (8 * j) =
    ∑ j ∈ Finset.range (8 * k), (src.val[j]!).val * 2 ^ (8 * j) +
    U8Slice_chunk_as_U64 src k * 2 ^ (64 * k) := by
  have h_split : 8 * (k + 1) = 8 * k + 8 := by ring
  rw [h_split, Finset.sum_range_add]
  have hsub : ∑ x ∈ Finset.range 8, (src.val[8 * k + x]!).val * 2 ^ (8 * (8 * k + x)) =
      U8Slice_chunk_as_U64 src k * 2 ^ (64 * k) := by
    unfold U8Slice_chunk_as_U64
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have h_exp : 8 * (8 * k + j) = 8 * j + 64 * k := by ring
    rw [h_exp, pow_add]
    ring
  rw [hsub]

private lemma chunk_sum_eq (src : Slice Std.U8) (n : ℕ) :
    ∑ j ∈ Finset.range (8 * n), (src.val[j]!).val * 2 ^ (8 * j) =
    ∑ k ∈ Finset.range n, U8Slice_chunk_as_U64 src k * 2 ^ (64 * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [chunk_step_identity src n, ih, Finset.sum_range_succ]

private lemma U64Slice_as_Nat_eq_chunk_sum
    (src : Slice Std.U8) (dst : Slice Std.U64) (n : ℕ)
    (h_inv : ∀ k < n, (dst.val[k]!).val = U8Slice_chunk_as_U64 src k) :
    U64Slice_as_Nat dst n =
    ∑ j ∈ Finset.range (8 * n), (src.val[j]!).val * 2 ^ (8 * j) := by
  unfold U64Slice_as_Nat
  rw [show ∑ k ∈ Finset.range n, (dst.val[k]!).val * 2 ^ (64 * k) =
       ∑ k ∈ Finset.range n, U8Slice_chunk_as_U64 src k * 2 ^ (64 * k) from
    Finset.sum_congr rfl (fun k hk => by rw [h_inv k (Finset.mem_range.mp hk)])]
  exact (chunk_sum_eq src n).symm

private lemma fromLEBytes_toNat_list (l : List Byte) :
    (BitVec.fromLEBytes l).toNat =
    ∑ j ∈ Finset.range l.length, (l[j]!).toNat * 2 ^ (8 * j) := by
  induction l with
  | nil => simp [BitVec.fromLEBytes]
  | cons b l ih =>
    unfold BitVec.fromLEBytes
    simp only [List.length_cons, Finset.sum_range_succ',
               List.getElem!_cons_zero, Nat.mul_zero, pow_zero, mul_one]
    have hcons : ∀ j, (b :: l)[j + 1]! = l[j]! :=
      fun j => List.getElem!_cons_eq_getElem!_sub b l (j + 1) (by omega)
    simp_rw [hcons, show ∀ j, 8 * (j + 1) = 8 * j + 8 from fun j => by ring,
             pow_add]
    simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.ofNat_pos, mul_lt_mul_iff_right₀,
    lt_add_iff_pos_right, zero_lt_one, BitVec.toNat_mod_cancel_of_lt, ← mul_assoc, ← Finset.sum_mul, ← ih]
    simp only [show 8 * (l.length + 1) = 8 * l.length + 8 from by ring]
    have h_b_lt : b.toNat < 2 ^ 8 := by scalar_tac
    have h_l_lt : (BitVec.fromLEBytes l).toNat < 2 ^ (8 * l.length) :=
      by scalar_tac
    set n := 8 * l.length + 8 with hn_def
    have h1 : (BitVec.setWidth n b).toNat = b.toNat := by
      simp only [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le h_b_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h3 : ((BitVec.setWidth n (BitVec.fromLEBytes l)) <<< 8).toNat =
              (BitVec.fromLEBytes l).toNat * 2 ^ 8 := by
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_l_lt
            (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      have:= Nat.mod_eq_of_lt (calc (BitVec.fromLEBytes l).toNat * 2 ^ 8
          < 2 ^ (8 * l.length) * 2 ^ 8 :=
              Nat.mul_lt_mul_of_pos_right h_l_lt (by positivity)
          _ = 2 ^ n := by rw [← pow_add])
      simp only [Nat.shiftLeft_eq]
      exact this
    have h_or : (BitVec.setWidth n b ||| BitVec.setWidth n (BitVec.fromLEBytes l) <<< 8).toNat =
                b.toNat ||| (BitVec.fromLEBytes l).toNat * 2 ^ 8 := by
      rw [BitVec.toNat_or, h1, h3]
    have :(BitVec.fromLEBytes l).toNat % 2 ^ n = (BitVec.fromLEBytes l).toNat := by
      apply Nat.mod_eq_of_lt
      grind
    simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, this] at h_or   ⊢
    have :=or_mul_pow_two_eq_add b.toNat (BitVec.fromLEBytes l).toNat 8 h_b_lt
    omega

@[step]
private theorem from_le_bytes_val_spec (bytes : Array Std.U8 8#usize) :
    lift (core.num.U64.from_le_bytes bytes) ⦃ result =>
      result.val = ∑ j ∈ Finset.range 8, (bytes[j]!).val * 2 ^ (8 * j) ⦄ := by
  apply spec_mono (core.num.U64.from_le_bytes.step_spec bytes)
  intro result hbv
  have h_val : result.val = (BitVec.fromLEBytes (bytes.val.map U8.bv)).toNat := by
    simp only [UScalar.val, hbv, BitVec.toNat_cast]
  rw [h_val, fromLEBytes_toNat_list]
  have hlen : (bytes.val.map U8.bv).length = 8 := by
    simp only [List.length_map]; scalar_tac
  rw [hlen]
  apply Finset.sum_congr rfl
  intro j hj
  have hj8 : j < 8 := Finset.mem_range.mp hj
  congr 1
  have hjlen : j < bytes.val.length := by scalar_tac
  simp only [Array.getElem!_Nat_eq]
  simp_lists
  grind

@[step]
private lemma Slice_U64_update_spec (s : Slice Std.U64) (j : Usize) (v : Std.U64)
    (hj : j.val < (Slice.len s).val) :
    Slice.update s j v ⦃ s' =>
      (∀ k, k ≠ j.val → (s'.val[k]!) = (s.val[k]!)) ∧
      (s'.val[j.val]!) = v ∧
      (Slice.len s').val = (Slice.len s).val ⦄ := by
  apply spec_mono (Slice.update_spec s j v (by scalar_tac))
  intro s' hs'
  subst hs'
  constructor
  · intro k hk
    have h := Slice.getElem!_Nat_set_ne s j k v hk.symm
    simp only [Slice.getElem!_Nat_eq] at h
    exact h
  constructor
  · have h := Slice.getElem!_Nat_set_eq s j j.val v ⟨rfl, by scalar_tac⟩
    simp only [Slice.getElem!_Nat_eq] at h
    exact h
  · simp only [Slice.len_val, Slice.set_length]

private lemma inv_step
    (src : Slice Std.U8) (dst s : Slice Std.U64) (i : ℕ)
    (v : Std.U64) (hv : v.val = U8Slice_chunk_as_U64 src i)
    (h_at_i : (s.val[i]!) = v)
    (h_other : ∀ k, k ≠ i → (s.val[k]!) = (dst.val[k]!))
    (h_inv : ∀ k < i, (dst.val[k]!).val = U8Slice_chunk_as_U64 src k) :
    ∀ k < i + 1, (s.val[k]!).val = U8Slice_chunk_as_U64 src k := by
  intro k hk
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
  · rw [congrArg (·.val) (h_other k (by omega))]
    exact h_inv k hlt
  · rw [congrArg (·.val) h_at_i, hv]

/-! ## The Main Spec Theorems -/

/- **Strong loop spec for `read_le_u64_into_loop`**:

    Starting from loop counter `i` with the element-correctness invariant
    `∀ k < i.val, dst.val[k].val = U8Slice_chunk_as_U64 src k`, the loop
    runs to completion and returns `result` satisfying the full invariant
    for all `k < n` (where `n = (Slice.len dst).val`).

    **Hypotheses**:
    - `hn` — identifies the loop bound `n` with the dst length.
    - `h_src_len` — length precondition `src.len = 8 * n`.
    - `hi` — loop counter in range: `i.val ≤ n`.
    - `h_inv` — element-correctness invariant for `k < i.val`.

    **Postconditions**:
    1. **Element correctness**: `∀ k < n, result.val[k].val = U8Slice_chunk_as_U64 src k`.
    2. **Combined value**: `U64Slice_as_Nat result n = ∑_{j<8n} src.val[j].val · 2^(8j)`.

    **Proof strategy**: Decreasing induction on `n − i.val`.
    - **Active branch** (`i < n`): the `step` tactic processes the 8
      `Slice.index_usize` calls and the `Slice.update` call;
      `from_le_bytes_val_spec` relates the assembled bytes to the
      `U8Slice_chunk_as_U64` value; `inv_step` extends the invariant.
    - **Base case** (`i = n`): the loop exits, the invariant directly gives
      postcondition 1, and `U64Slice_as_Nat_eq_chunk_sum` + `chunk_sum_eq`
      establish postcondition 2.
-/


private theorem read_le_u64_into_loop_spec_strong
    (src : Slice Std.U8) (dst : Slice Std.U64) (i : Std.Usize)
    (n : ℕ) (hn : n = (Slice.len dst).val)
    (h_src_len : (Slice.len src).val = 8 * n)
    (hi : i.val ≤ n)
    (h_inv : ∀ k < i.val, (dst.val[k]!).val = U8Slice_chunk_as_U64 src k) :
    read_le_u64_into_loop src dst i ⦃ result =>
      (∀ k < n, (result.val[k]!).val = U8Slice_chunk_as_U64 src k) ∧
      U64Slice_as_Nat result n =
        ∑ j ∈ Finset.range (8 * n), (src.val[j]!).val * 2 ^ (8 * j) ⦄ := by
  unfold read_le_u64_into_loop
  simp only [UScalar.lt_equiv, Usize.ofNatCore_val_eq]
  split
  case isTrue hlt =>
    have hi' : i.val < n := by scalar_tac
    step as ⟨start, hstart⟩
    have hstart_val : start.val = 8 * i.val := by scalar_tac
    step as ⟨b0, hb0⟩
    step as ⟨off1, hoff1⟩; step as ⟨b1, hb1⟩
    step as ⟨off2, hoff2⟩; step as ⟨b2, hb2⟩
    step as ⟨off3, hoff3⟩; step as ⟨b3, hb3⟩
    step as ⟨off4, hoff4⟩; step as ⟨b4, hb4⟩
    step as ⟨off5, hoff5⟩; step as ⟨b5, hb5⟩
    step as ⟨off6, hoff6⟩; step as ⟨b6, hb6⟩
    step as ⟨off7, hoff7⟩; step as ⟨b7, hb7⟩
    step with from_le_bytes_val_spec (Array.make 8#usize [b0, b1, b2, b3, b4, b5, b6, b7])
      as ⟨v, hv⟩
    step with Slice_U64_update_spec dst i v (by scalar_tac) as ⟨dst', hdst'_other, hdst'_at, hdst'_len⟩
    step as ⟨i', hi'_step⟩
    have hi'_eq : i'.val = i.val + 1 := by scalar_tac
    have hoff1_val : off1.val = 8 * i.val + 1 := by scalar_tac
    have hoff2_val : off2.val = 8 * i.val + 2 := by scalar_tac
    have hoff3_val : off3.val = 8 * i.val + 3 := by scalar_tac
    have hoff4_val : off4.val = 8 * i.val + 4 := by scalar_tac
    have hoff5_val : off5.val = 8 * i.val + 5 := by scalar_tac
    have hoff6_val : off6.val = 8 * i.val + 6 := by scalar_tac
    have hoff7_val : off7.val = 8 * i.val + 7 := by scalar_tac
    have hb0_src : b0 = src.val[8 * i.val + 0]! := by
      have h : b0 = src.val[start.val]! := by simp [hb0]
      grind only
    have hb1_src : b1 = src.val[8 * i.val + 1]! := by
      have h : b1 = src.val[off1.val]! := by simp [hb1]
      grind only
    have hb2_src : b2 = src.val[8 * i.val + 2]! := by
      have h : b2 = src.val[off2.val]! := by simp [hb2]
      grind only
    have hb3_src : b3 = src.val[8 * i.val + 3]! := by
      have h : b3 = src.val[off3.val]! := by simp [hb3]
      grind only
    have hb4_src : b4 = src.val[8 * i.val + 4]! := by
      have h : b4 = src.val[off4.val]! := by simp [hb4]
      grind only
    have hb5_src : b5 = src.val[8 * i.val + 5]! := by
      have h : b5 = src.val[off5.val]! := by simp [hb5]
      grind only
    have hb6_src : b6 = src.val[8 * i.val + 6]! := by
      have h : b6 = src.val[off6.val]! := by simp [hb6]
      grind only
    have hb7_src : b7 = src.val[8 * i.val + 7]! := by
      have h : b7 = src.val[off7.val]! := by simp [hb7]
      grind only
    have h_chunk : v.val = U8Slice_chunk_as_U64 src i.val := by
      rw [hv]
      unfold U8Slice_chunk_as_U64
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
                 Array.getElem!_Nat_eq, Array.make,
                 hb0_src, hb1_src, hb2_src, hb3_src, hb4_src, hb5_src, hb6_src, hb7_src]
      grind only [= List.getElem!_length_le, = getElem!_pos, = List.getElem!_cons_eq_getElem!_sub,
    = List.getElem!_cons_zero', usr Usize.cMax_bound, usr Usize.cMax_bound', usr Isize.cMax_bound',
    usr Isize.cMax_bound, = UScalar.default_val]
    have h_inv' : ∀ k < i'.val, (dst'.val[k]!).val = U8Slice_chunk_as_U64 src k := by
      rw [hi'_eq]
      exact inv_step src dst dst' i.val v h_chunk hdst'_at hdst'_other h_inv
    have hn' : n = (Slice.len dst').val := by rw [hdst'_len]; exact hn
    apply spec_mono
      (read_le_u64_into_loop_spec_strong src dst' i' n hn' h_src_len (by omega) h_inv')
    intro result ⟨h_elem, h_nat⟩
    exact ⟨h_elem, h_nat⟩
  case isFalse hge =>
    have hi_eq : i.val = n := by scalar_tac
    rw [spec_ok]
    refine ⟨fun k hk => h_inv k (by omega), ?_⟩
    -- Combined value: U64Slice_as_Nat dst n = ∑_{j<8n} src[j] * 2^(8j)
    rw[hi_eq] at h_inv
    exact U64Slice_as_Nat_eq_chunk_sum src dst n h_inv
  termination_by n - i.val
  decreasing_by
    simp only [hi'_eq]
    omega

@[step]
theorem read_le_u64_into_loop_spec
    (src : Slice Std.U8) (dst : Slice Std.U64) (i : Std.Usize)
    (n : ℕ) (hn : n = (Slice.len dst).val)
    (h_src_len : (Slice.len src).val = 8 * n)
    (hi : i.val ≤ n)
    (h_inv : ∀ k < i.val, (dst.val[k]!).val = U8Slice_chunk_as_U64 src k) :
    read_le_u64_into_loop src dst i ⦃ result =>
      (∀ k < n, (result.val[k]!).val = U8Slice_chunk_as_U64 src k) ∧
      U64Slice_as_Nat result n =
        ∑ j ∈ Finset.range (8 * n), (src.val[j]!).val * 2 ^ (8 * j) ⦄ :=
  read_le_u64_into_loop_spec_strong src dst i n hn h_src_len hi h_inv

@[step]
theorem read_le_u64_into_spec
    (src : Slice Std.U8) (dst : Slice Std.U64)
    (n : ℕ) (hn : n = (Slice.len dst).val)
    (h_src_len : (Slice.len src).val = 8 * n) :
    read_le_u64_into src dst ⦃ result =>
      (∀ k < n, (result.val[k]!).val = U8Slice_chunk_as_U64 src k) ∧
      U64Slice_as_Nat result n =
        ∑ j ∈ Finset.range (8 * n), (src.val[j]!).val * 2 ^ (8 * j) ⦄ := by
  simp only [read_le_u64_into]
  step as ⟨len_src_eq, _⟩
  step
  step as ⟨len8, hlen8⟩
  simp_all

theorem read_le_u64_into_combined_value
    (src : Slice Std.U8) (dst : Slice Std.U64)
    (n : ℕ) (hn : n = (Slice.len dst).val)
    (h_src_len : (Slice.len src).val = 8 * n) :
    read_le_u64_into src dst ⦃ result =>
      U64Slice_as_Nat result n =
        ∑ j ∈ Finset.range (8 * n), (src.val[j]!).val * 2 ^ (8 * j) ⦄ := by
  apply spec_mono (read_le_u64_into_spec src dst n hn h_src_len)
  intro result ⟨_, h_nat⟩
  exact h_nat

end curve25519_dalek.scalar
