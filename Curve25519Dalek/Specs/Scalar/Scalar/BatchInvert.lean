/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.TypesAux
import Curve25519Dalek.Specs.Scalar.Scalar.Unpack
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.AsMontgomery
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryInvert
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromMontgomery
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::batch_invert`

Computes the multiplicative inverses of a batch of scalars in-place using
Montgomery's batch-inversion trick.

## Algorithm overview

Let `n = inputs.len()`, `L` the group order, and `R = 2^260` the Montgomery
constant.  Write `vals : ℕ → ℕ` for the original scalar values:
`vals j = U8x32_as_Nat inputs[j].bytes` before any mutation.

**Setup** (lines 796–803):
- `one = ONE.unpack().as_montgomery()`:
    `Scalar52_as_Nat one ≡ R  [MOD L]`  (the Montgomery form of 1).
- `scratch = vec![one; n]`:  a length-`n` scratch vector, pre-filled with `one`.
- `acc = one`:  the running accumulator, initialised to `one`.

**Forward pass** (`batch_invert_loop0`, lines 808–818, iterations 0 … n−1):
At step `i`:
  - `scratch[i] ← acc`          (saves prefix product `R · ∏_{j < i} vals j`)
  - `tmp ← inputs[i].unpack().as_montgomery()`
    (`Scalar52_as_Nat tmp ≡ vals i · R  [MOD L]`)
  - `inputs[i] ← tmp.pack()`    (overwrites input with its Montgomery form)
  - `acc ← montgomery_mul(acc, tmp)` (extends prefix product)

Loop invariant at counter `i` (with `A = R`):
  1. `Scalar52_as_Nat acc ≡ A · PrefixProd vals i  [MOD L]`
  2. `∀ j < i, scratch[j] ≡ A · PrefixProd vals j  [MOD L]`
  3. `∀ j < i, U8x32_as_Nat inputs[j].bytes ≡ vals j · R  [MOD L]`
  4. `∀ j, i ≤ j < n, U8x32_as_Nat inputs[j].bytes = vals j`  (untouched)

On exit: `Scalar52_as_Nat acc1 ≡ R · ∏_{j < n} vals j  [MOD L]`.

**Inversion** (lines 823–828):
- Assert `pack(acc1) ≠ ZERO`  (product is nonzero when all inputs are).
- `s2 ← montgomery_invert(acc1)`:
    `Scalar52_as_Nat acc1 · Scalar52_as_Nat s2 ≡ R²  [MOD L]`.
- `acc2 ← from_montgomery(s2)`:
    `Scalar52_as_Nat acc2 · R ≡ Scalar52_as_Nat s2  [MOD L]`.
- Together (proved in `batch_invert_acc2_inv`):
    `Scalar52_as_Nat acc2 · PrefixProd vals n ≡ 1  [MOD L]`.
- `ret ← pack(acc2)`:
    `U8x32_as_Nat ret.bytes · PrefixProd vals n ≡ 1  [MOD L]`.

**Backward pass** (`batch_invert_loop1`, lines 832–839, iterations n … 1):
At step `k = i − 1` (from `n − 1` down to `0`):
  - `inputs[k] ← montgomery_mul(acc, scratch[k]).pack()`   (individual inverse)
  - `acc         ← montgomery_mul(acc, inputs[k].unpack())`  (new accumulator)

Loop invariant at counter `i` (with parameter `P = 1`):
  - `Scalar52_as_Nat acc · PrefixProd vals i ≡ 1  [MOD L]`
  - `∀ j, i ≤ j < n, U8x32_as_Nat inputs[j].bytes · vals j ≡ 1  [MOD L]`

On exit: `∀ j < n, U8x32_as_Nat inputs2[j].bytes · vals j ≡ 1  [MOD L]`.

**Return**: `(ret, inputs2)` where `ret` is the inverse of the full product and
each `inputs2[j]` is the multiplicative inverse of the original `inputs[j]`.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

-- `#setup_aeneas_simps` uses a `#` command which triggers the hashCommand linter;
-- suppressed intentionally.
set_option linter.hashCommand false
-- R = 2^260 in the Montgomery domain; prevents kernel exponentiation explosion.
set_option exponentiation.threshold 260
#setup_aeneas_simps
attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Auxiliary Element-Access Predicates

The `Vec` and `Slice` invariants express "the j-th element of a container satisfies
property P".  We use `l[j]?`-based predicates (the Lean 4 `GetElem?` notation)
so that no `Inhabited` instance for `Scalar52` or `Scalar` is required. -/

/-- `Vec52At v j P` holds iff the j-th entry of the Vec (when it exists) satisfies `P`. -/
def Vec52At
    (v : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (j : ℕ)
    (P : backend.serial.u64.scalar.Scalar52 → Prop) : Prop :=
  ∀ x : backend.serial.u64.scalar.Scalar52,
    (v.val : List backend.serial.u64.scalar.Scalar52)[j]? = some x → P x

/-- `SliceScalarAt sl j P` holds iff the j-th scalar in the slice (when it exists)
    satisfies `P` applied to its `bytes`. -/
def SliceScalarAt
    (sl : Slice scalar.Scalar)
    (j : ℕ)
    (P : Array Std.U8 32#usize → Prop) : Prop :=
  ∀ x : scalar.Scalar,
    (sl.val : List scalar.Scalar)[j]? = some x → P x.bytes

/-! ## Mathematical Definitions -/

/-- The prefix product of a natural-number sequence:
    `PrefixProd vals k = ∏_{j < k} vals j`. -/
def PrefixProd (vals : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∏ j ∈ Finset.range k, vals j

/-! ## Basic Properties of `PrefixProd` -/

@[simp]
lemma PrefixProd_zero (vals : ℕ → ℕ) : PrefixProd vals 0 = 1 := by
  simp [PrefixProd]

lemma PrefixProd_succ (vals : ℕ → ℕ) (k : ℕ) :
    PrefixProd vals (k + 1) = PrefixProd vals k * vals k := by
  simp [PrefixProd, Finset.prod_range_succ]

private lemma acc_inv_step
    (acc tmp acc' : backend.serial.u64.scalar.Scalar52)
    (A : ℕ) (vals : ℕ → ℕ) (i : ℕ)
    (h_acc : Scalar52_as_Nat acc ≡ A * PrefixProd vals i [MOD L])
    (h_tmp : Scalar52_as_Nat tmp ≡ vals i * R [MOD L])
    (h_mul : Scalar52_as_Nat acc * Scalar52_as_Nat tmp
             ≡ Scalar52_as_Nat acc' * R [MOD L]) :
    Scalar52_as_Nat acc' ≡ A * PrefixProd vals (i + 1) [MOD L] :=
  cancelR <|
    h_mul.symm.trans <| by
      calc Scalar52_as_Nat acc * Scalar52_as_Nat tmp
          ≡ (A * PrefixProd vals i) * (vals i * R) [MOD L] :=
              Nat.ModEq.mul h_acc h_tmp
        _ = A * PrefixProd vals (i + 1) * R := by rw [PrefixProd_succ]; ring

private lemma scratch_inv_step
    (scratch scratch0 : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52)
    (A : ℕ) (vals : ℕ → ℕ) (i : ℕ)
    (h_inv : ∀ j < i,
        Vec52At scratch j (fun x => Scalar52_as_Nat x ≡ A * PrefixProd vals j [MOD L]))
    (h_acc : Scalar52_as_Nat acc ≡ A * PrefixProd vals i [MOD L])
    (h_new : (scratch0.val : List backend.serial.u64.scalar.Scalar52)[i]? = some acc)
    (h_old : ∀ j, j ≠ i →
        (scratch0.val : List backend.serial.u64.scalar.Scalar52)[j]? =
        (scratch.val : List backend.serial.u64.scalar.Scalar52)[j]?) :
    ∀ j < i + 1,
        Vec52At scratch0 j (fun x => Scalar52_as_Nat x ≡ A * PrefixProd vals j [MOD L]) := by
  intro j hj x hx
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | rfl
  · rw [h_old j (Nat.ne_of_lt hjlt)] at hx
    exact h_inv j hjlt x hx
  · rw [h_new] at hx
    exact Option.some.inj hx ▸ h_acc

private lemma inp_mont_step
    (inputs inputs0 : Slice scalar.Scalar)
    (input1 : scalar.Scalar)
    (vals : ℕ → ℕ) (i : ℕ)
    (h_inv : ∀ j < i,
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]))
    (h_new : U8x32_as_Nat input1.bytes ≡ vals i * R [MOD L])
    (h_elem : (inputs0.val : List scalar.Scalar)[i]? = some input1)
    (h_rest : ∀ j, j ≠ i →
        (inputs0.val : List scalar.Scalar)[j]? =
        (inputs.val : List scalar.Scalar)[j]?) :
    ∀ j < i + 1,
        SliceScalarAt inputs0 j (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]) := by
  intro j hj x hx
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | rfl
  · rw [h_rest j (Nat.ne_of_lt hjlt)] at hx
    exact h_inv j hjlt x hx
  · rw [h_elem] at hx
    exact Option.some.inj hx ▸ h_new

private lemma inp_orig_step
    (inputs inputs0 : Slice scalar.Scalar)
    (vals : ℕ → ℕ) (n i : ℕ)
    (h_orig : ∀ j, i ≤ j → j < n →
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b = vals j))
    (h_rest : ∀ j, j ≠ i →
        (inputs0.val : List scalar.Scalar)[j]? =
        (inputs.val : List scalar.Scalar)[j]?) :
    ∀ j, i + 1 ≤ j → j < n →
        SliceScalarAt inputs0 j (fun b => U8x32_as_Nat b = vals j) := by
  intro j hj1 hj2 x hx
  rw [h_rest j (by omega)] at hx
  exact h_orig j (by omega) hj2 x hx

/-! ## The Main Inductive Proof (Strong Form) -/

/- **Stronger loop 0 spec** tracking all four invariant components simultaneously.

    Invariants maintained at loop counter `i`:
    1. `Scalar52_as_Nat acc ≡ A · PrefixProd vals i  [MOD L]`
    2. `∀ j < i, Vec52At scratch j (val(·) ≡ A · PrefixProd vals j)`
    3. `∀ j < i, SliceScalarAt inputs j (U8x32_as_Nat · ≡ vals j · R)`
    4. `∀ i ≤ j < n, SliceScalarAt inputs j (U8x32_as_Nat · = vals j)`

    On exit (i = n): `result = (inputs', scratch', acc')` satisfies (1)–(3) for `n`.  -/

set_option maxHeartbeats 1000000 in -- large inductive proof over loop requires extra heartbeats.
private theorem batch_invert_loop0_spec_strong
    (inputs : Slice scalar.Scalar) (n : Std.Usize)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52) (i : Std.Usize)
    (hi : i.val ≤ n.val)
    (h_inputs_len : inputs.val.length = n.val)
    (h_scratch_len : scratch.val.length = n.val)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L)
    (A : ℕ)
    (vals : ℕ → ℕ)
    (h_vals_lt : ∀ j < n.val, vals j < L)
    (h_acc_inv : Scalar52_as_Nat acc ≡ A * PrefixProd vals i.val [MOD L])
    (h_scratch_inv : ∀ j < i.val,
        Vec52At scratch j
          (fun x => Scalar52_as_Nat x ≡ A * PrefixProd vals j [MOD L]))
    (h_inp_mont : ∀ j < i.val,
        SliceScalarAt inputs j
          (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]))
    (h_inp_orig : ∀ j, i.val ≤ j → j < n.val →
        SliceScalarAt inputs j
          (fun b => U8x32_as_Nat b = vals j)) :
    batch_invert_loop0 inputs n scratch acc i ⦃ (result :
        Slice scalar.Scalar × alloc.vec.Vec backend.serial.u64.scalar.Scalar52 ×
        backend.serial.u64.scalar.Scalar52) =>
      Scalar52_as_Nat result.2.2 ≡ A * PrefixProd vals n.val [MOD L] ∧
      (∀ j < n.val,
          Vec52At result.2.1 j
            (fun x => Scalar52_as_Nat x ≡ A * PrefixProd vals j [MOD L])) ∧
      (∀ j < n.val,
          SliceScalarAt result.1 j
            (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L])) ∧
      (∀ i < 5, result.2.2[i]!.val < 2 ^ 52) ∧
      (Scalar52_as_Nat result.2.2 < L) ∧
      result.1.val.length = n.val ∧
      result.2.1.val.length = n.val ⦄ := by
  unfold batch_invert_loop0
  split
  case isTrue hlt =>
    have hi_lt : i.val < n.val := by scalar_tac
    have hbound_inputs : i.val < inputs.length := by
      simp only [Slice.length]; omega
    have hbound_scratch : i.val < scratch.length := by
      grind
    simp only [alloc.vec.Vec.index_mut_slice_index]
    haveI : Inhabited scalar.Scalar := ⟨{ bytes := Array.repeat 32#usize 0#u8 }⟩
    haveI : Inhabited backend.serial.u64.scalar.Scalar52 := ⟨Array.repeat 5#usize 0#u64⟩
    step with Slice.index_mut_usize_spec as ⟨  input, index_mut_back⟩
    step with alloc.vec.Vec.index_mut_usize_spec scratch i as ⟨_, _, _, h_vec_back⟩
    step
    step
    step
    -- Auxiliary bounds for montgomery_mul
    have hacc_limbs62 : ∀ j < 5, acc[j]!.val < 2 ^ 62 :=
      fun j hj => Nat.lt_trans (h_acc_limbs j hj) (by norm_num)
    have htmp_limbs62 : ∀ j < 5, tmp[j]!.val < 2 ^ 62 := by grind
    have hLpos : (0 : ℕ) < L := by unfold L; norm_num
    have hLR : L ≤ R := Nat.le_of_lt (by unfold L R; grind)
    have hval_bound : Scalar52_as_Nat acc * Scalar52_as_Nat tmp < R * L := by
      cases Nat.eq_zero_or_pos (Scalar52_as_Nat tmp) with
      | inl h =>
        rw [h, Nat.mul_zero]
        exact Nat.mul_pos (Nat.lt_of_lt_of_le hLpos hLR) hLpos
      | inr hpos =>
        calc Scalar52_as_Nat acc * Scalar52_as_Nat tmp
            < L * Scalar52_as_Nat tmp :=
              Nat.mul_lt_mul_of_pos_right h_acc_lt hpos
          _ < L * L := by
              apply Nat.mul_lt_mul_of_pos_left
              all_goals  grind
          _ ≤ R * L :=
              Nat.mul_le_mul hLR (le_refl L)
    step
    step as ⟨i1, hi1_val⟩
    have hi1_succ : i1.val = i.val + 1 := by scalar_tac
    have hinput_nat : U8x32_as_Nat input.1.bytes = vals i.val := by
      have hslice_at := h_inp_orig i.val le_rfl hi_lt
      unfold SliceScalarAt at hslice_at
      apply hslice_at input.1
      have hlen : i.val < inputs.val.length := by omega
      have h1 := @List.getElem?_eq_getElem _ inputs.val i.val hlen
      rw [h1]
      simp_all
    have hs_val : Scalar52_as_Nat s = vals i.val := by
      simp_all
    have htmp_vals_R : Scalar52_as_Nat tmp ≡ vals i.val * R [MOD L] := by
      simp_all
    have hinput1_vals_R : U8x32_as_Nat input1.bytes ≡ vals i.val * R [MOD L] :=
      input1_post1.trans htmp_vals_R
    have hacc1_inv : Scalar52_as_Nat acc1 ≡ A * PrefixProd vals i1.val [MOD L] := by
      rw [hi1_succ]
      exact acc_inv_step acc tmp acc1 A vals i.val h_acc_inv htmp_vals_R acc1_post1
    have hs1_len : (Slice.set inputs i input1).val.length = n.val := by
      simp [Slice.set_val_eq, List.length_set, h_inputs_len]
    have hscratch1_len : (Slice.set scratch i acc).val.length = n.val := by
      simp [ List.length_set, h_scratch_len]
    have h_scratch_new : (Slice.set scratch i acc).val[i.val]? = some acc := by
      simp only [Slice.set_val_eq]
      exact List.getElem?_set_self (h_scratch_len ▸ hi_lt)
    have h_scratch_old : ∀ j, j ≠ i.val →
        (Slice.set scratch i acc).val[j]? = scratch.val[j]? := by
      intro j hj
      simp
      grind
    have h_inp_elem : (Slice.set inputs i input1).val[i.val]? = some input1 := by
      simp only [Slice.set_val_eq]
      exact List.getElem?_set_self (h_inputs_len ▸ hi_lt)
    have h_inp_rest : ∀ j, j ≠ i.val →
        (Slice.set inputs i input1).val[j]? = inputs.val[j]? := by
      intro j hj
      simp
      grind
    have h_scratch_inv' : ∀ j < i1.val,
        Vec52At (Slice.set scratch i acc) j
          (fun x => Scalar52_as_Nat x ≡ A * PrefixProd vals j [MOD L]) := by
      rw [hi1_succ]
      exact scratch_inv_step scratch (Slice.set scratch i acc) acc A vals i.val
        h_scratch_inv h_acc_inv h_scratch_new h_scratch_old
    have h_inp_mont' : ∀ j < i1.val,
        SliceScalarAt (Slice.set inputs i input1) j
          (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]) := by
      rw [hi1_succ]
      exact inp_mont_step inputs (Slice.set inputs i input1) input1 vals i.val
        h_inp_mont hinput1_vals_R h_inp_elem h_inp_rest
    have h_inp_orig' : ∀ j, i1.val ≤ j → j < n.val →
        SliceScalarAt (Slice.set inputs i input1) j
          (fun b => U8x32_as_Nat b = vals j) := by
      rw [hi1_succ]
      exact inp_orig_step inputs (Slice.set inputs i input1) vals n.val i.val
        h_inp_orig h_inp_rest
    have hacc1_limbs : ∀ j < 5, acc1[j]!.val < 2 ^ 52 := by grind
    have hacc1_lt : Scalar52_as_Nat acc1 < L := by grind
    simp only [index_mut_back, h_vec_back]
    exact spec_mono
      (batch_invert_loop0_spec_strong
        (Slice.set inputs i input1) n (Slice.set scratch i acc) acc1 i1
        (by omega)
        hs1_len
        hscratch1_len
        hacc1_limbs hacc1_lt
        A vals h_vals_lt
        hacc1_inv
        h_scratch_inv'
        h_inp_mont'
        h_inp_orig'
        )
      (fun result hresult => hresult)
  case isFalse hge =>
    have hi_eq : i.val = n.val := by grind
    simp only [spec_ok]
    refine ⟨?_, ?_, ?_⟩
    · rwa [hi_eq] at h_acc_inv
    · intro j hj; exact h_scratch_inv j (hi_eq ▸ hj)
    · constructor
      · intro j hj; exact h_inp_mont j (hi_eq ▸ hj)
      · constructor
        · intro i hi; grind
        · exact ⟨by grind, h_inputs_len, h_scratch_len⟩
  termination_by n.val - i.val
  decreasing_by scalar_tac


/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::batch_invert_loop0`**
• The function always terminates and succeeds for any valid `inputs`, `scratch`, `acc`,
  and `i ≤ n`.
• **Accumulator**: `Scalar52_as_Nat acc' ≡ A · ∏_{j < n} vals(j)  [MOD L]`
  where `A = Scalar52_as_Nat acc_init` and `vals(j) = U8x32_as_Nat inputs_orig[j].bytes`.
• **Scratch**: for all `j < n` and any `x = scratch'[j]`,
  `Scalar52_as_Nat x ≡ A · ∏_{m < j} vals(m)  [MOD L]`.
• **Inputs**: for all `j < n` and any `inp = inputs'[j]`,
  `U8x32_as_Nat inp.bytes ≡ vals(j) · R  [MOD L]`
  (every original input has been replaced by its Montgomery form).
-/
@[step]
theorem batch_invert_loop0_spec
    (inputs : Slice scalar.Scalar) (n : Std.Usize)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52) (i : Std.Usize)
    (hi : i.val ≤ n.val)
    (h_inputs_len : inputs.val.length = n.val)
    (h_scratch_len : scratch.val.length = n.val)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L)
    (A : ℕ)
    (vals : ℕ → ℕ)
    (h_vals_lt : ∀ j < n.val, vals j < L)
    (h_acc_inv : Scalar52_as_Nat acc ≡ A * PrefixProd vals i.val [MOD L])
    (h_scratch_inv : ∀ j < i.val,
        Vec52At scratch j
          (fun x => Scalar52_as_Nat x ≡ A * PrefixProd vals j [MOD L]))
    (h_inp_mont : ∀ j < i.val,
        SliceScalarAt inputs j
          (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]))
    (h_inp_orig : ∀ j, i.val ≤ j → j < n.val →
        SliceScalarAt inputs j
          (fun b => U8x32_as_Nat b = vals j)) :
    batch_invert_loop0 inputs n scratch acc i ⦃ (result :
        Slice scalar.Scalar × alloc.vec.Vec backend.serial.u64.scalar.Scalar52 ×
        backend.serial.u64.scalar.Scalar52) =>
      Scalar52_as_Nat result.2.2 ≡ A * PrefixProd vals n.val [MOD L] ∧
      (∀ j < n.val,
          Vec52At result.2.1 j
            (fun x => Scalar52_as_Nat x ≡ A * PrefixProd vals j [MOD L])) ∧
      (∀ j < n.val,
          SliceScalarAt result.1 j
            (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L])) ∧
      (∀ i < 5, result.2.2[i]!.val < 2 ^ 52) ∧
      (Scalar52_as_Nat result.2.2 < L) ∧
      result.1.val.length = n.val ∧
      result.2.1.val.length = n.val ⦄ :=
  batch_invert_loop0_spec_strong
    inputs n scratch acc i
    hi h_inputs_len h_scratch_len
    h_acc_limbs h_acc_lt
    A vals h_vals_lt
    h_acc_inv h_scratch_inv h_inp_mont h_inp_orig

private lemma acc_inv_step_loop1
    (acc tmp s : backend.serial.u64.scalar.Scalar52)
    (vals : ℕ → ℕ) (k : ℕ) (P : ℕ)
    (h_acc : Scalar52_as_Nat acc * PrefixProd vals (k + 1) ≡ P [MOD L])
    (h_s : Scalar52_as_Nat s ≡ vals k * R [MOD L])
    (h_mul : Scalar52_as_Nat acc * Scalar52_as_Nat s
             ≡ Scalar52_as_Nat tmp * R [MOD L]) :
    Scalar52_as_Nat tmp * PrefixProd vals k ≡ P [MOD L] := by
  have h_key : Scalar52_as_Nat tmp * PrefixProd vals k ≡
               Scalar52_as_Nat acc * PrefixProd vals (k + 1) [MOD L] := by
    apply cancelR
    calc Scalar52_as_Nat tmp * PrefixProd vals k * R
        = Scalar52_as_Nat tmp * R * PrefixProd vals k := by ring
      _ ≡ Scalar52_as_Nat acc * Scalar52_as_Nat s * PrefixProd vals k [MOD L] :=
          h_mul.symm.mul_right _
      _ ≡ Scalar52_as_Nat acc * (vals k * R) * PrefixProd vals k [MOD L] :=
          (h_s.mul_left _).mul_right _
      _ = Scalar52_as_Nat acc * PrefixProd vals (k + 1) * R := by
          rw [PrefixProd_succ]; ring
  exact h_key.trans h_acc

private lemma inp_inv_step_loop1
    (acc scratch_val : backend.serial.u64.scalar.Scalar52)
    (s1_val : ℕ) (b : Array Std.U8 32#usize)
    (vals : ℕ → ℕ) (k : ℕ) (P : ℕ)
    (h_acc : Scalar52_as_Nat acc * PrefixProd vals (k + 1) ≡ P [MOD L])
    (h_scratch : Scalar52_as_Nat scratch_val ≡ R * PrefixProd vals k [MOD L])
    (h_s1 : Scalar52_as_Nat acc * Scalar52_as_Nat scratch_val
                 ≡ s1_val * R [MOD L])
    (h_pack : U8x32_as_Nat b ≡ s1_val [MOD L]) :
    U8x32_as_Nat b * vals k ≡ P [MOD L] := by
  have h_s1_val : s1_val ≡ Scalar52_as_Nat acc * PrefixProd vals k [MOD L] := by
    apply cancelR
    calc s1_val * R
        ≡ Scalar52_as_Nat acc * Scalar52_as_Nat scratch_val [MOD L] := h_s1.symm
      _ ≡ Scalar52_as_Nat acc * (R * PrefixProd vals k) [MOD L] :=
          h_scratch.mul_left _
      _ = Scalar52_as_Nat acc * PrefixProd vals k * R := by ring
  calc U8x32_as_Nat b * vals k
      ≡ s1_val * vals k [MOD L] := h_pack.mul_right _
    _ ≡ Scalar52_as_Nat acc * PrefixProd vals k * vals k [MOD L] :=
        h_s1_val.mul_right _
    _ = Scalar52_as_Nat acc * PrefixProd vals (k + 1) := by rw [PrefixProd_succ]; ring
    _ ≡ P [MOD L] := h_acc

private lemma inp_inv_suffix_step
    (inputs inputs0 : Slice scalar.Scalar)
    (vals : ℕ → ℕ) (n k : ℕ) (P : ℕ) (input1 : scalar.Scalar)
    (h_inv : ∀ j, k + 1 ≤ j → j < n →
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b * vals j ≡ P [MOD L]))
    (h_new : U8x32_as_Nat input1.bytes * vals k ≡ P [MOD L])
    (h_elem : (inputs0.val : List scalar.Scalar)[k]? = some input1)
    (h_rest : ∀ j, j ≠ k →
        (inputs0.val : List scalar.Scalar)[j]? =
        (inputs.val : List scalar.Scalar)[j]?) :
    ∀ j, k ≤ j → j < n →
        SliceScalarAt inputs0 j (fun b => U8x32_as_Nat b * vals j ≡ P [MOD L]) := by
  intro j hj1 hj2 x hx
  by_cases hjk : j = k
  · subst hjk; rw [h_elem] at hx; exact Option.some.inj hx ▸ h_new
  · rw [h_rest j hjk] at hx; exact h_inv j (by omega) hj2 x hx

private lemma inp_mont_prefix_step
    (inputs inputs0 : Slice scalar.Scalar)
    (vals : ℕ → ℕ) (k : ℕ)
    (h_mont : ∀ j < k,
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]))
    (h_rest : ∀ j, j ≠ k →
        (inputs0.val : List scalar.Scalar)[j]? =
        (inputs.val : List scalar.Scalar)[j]?) :
    ∀ j < k,
        SliceScalarAt inputs0 j (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]) := by
  intro j hj x hx; rw [h_rest j (by omega)] at hx; exact h_mont j hj x hx

private lemma inp_lt_prefix_step
    (inputs inputs0 : Slice scalar.Scalar)
    (k B : ℕ)
    (h_lt : ∀ j < k, SliceScalarAt inputs j (fun b => U8x32_as_Nat b < B))
    (h_rest : ∀ j, j ≠ k →
        (inputs0.val : List scalar.Scalar)[j]? =
        (inputs.val : List scalar.Scalar)[j]?) :
    ∀ j < k, SliceScalarAt inputs0 j (fun b => U8x32_as_Nat b < B) := by
  intro j hj x hx; rw [h_rest j (by omega)] at hx; exact h_lt j hj x hx

/-! ## The Main Inductive Proof (Strong Form) -/

private theorem batch_invert_loop1_spec_strong
    (inputs : Slice scalar.Scalar)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52) (i n : Std.Usize)
    (hi : i.val ≤ n.val)
    (h_inputs_len : inputs.val.length = n.val)
    (h_scratch_len : scratch.val.length = n.val)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L)
    (h_scratch_limbs : ∀ j < n.val,
        Vec52At scratch j
          (fun x => (∀ k < 5, x[k]!.val < 2 ^ 52) ∧ Scalar52_as_Nat x < L))
    (vals : ℕ → ℕ)
    (h_vals_lt : ∀ j < n.val, vals j < L)
    (P : ℕ)
    (h_acc_inv : Scalar52_as_Nat acc * PrefixProd vals i.val ≡ P [MOD L])
    (h_inp_inv : ∀ j, i.val ≤ j → j < n.val →
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b * vals j ≡ P [MOD L]))
    (h_inp_mont : ∀ j < i.val,
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]))
    (h_inp_mont_lt : ∀ j < i.val,
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b < L))
    (h_scratch_inv : ∀ j < n.val,
        Vec52At scratch j
          (fun x => Scalar52_as_Nat x ≡ R * PrefixProd vals j [MOD L])) :
    batch_invert_loop1 inputs scratch acc i ⦃ (result : Slice scalar.Scalar) =>
      ∀ j < n.val,
          SliceScalarAt result j (fun b => U8x32_as_Nat b * vals j ≡ P [MOD L]) ⦄ := by
  unfold batch_invert_loop1
  split
  case isTrue hlt =>
    have hi_pos : 0 < i.val := by scalar_tac
    step as ⟨i1, hi1_val⟩
    have hi1_eq : i1.val = i.val - 1 := by scalar_tac
    have hk_lt : i1.val < n.val := by omega
    haveI : Inhabited scalar.Scalar := ⟨{ bytes := Array.repeat 32#usize 0#u8 }⟩
    haveI : Inhabited backend.serial.u64.scalar.Scalar52 := ⟨Array.repeat 5#usize 0#u64⟩
    step with Slice.index_mut_usize_spec as ⟨input, index_mut_back⟩
    have h_input_mont : U8x32_as_Nat input.1.bytes ≡ vals i1.val * R [MOD L] := by
      apply h_inp_mont i1.val (by omega)
      have hlen : i1.val < inputs.val.length := h_inputs_len ▸ hk_lt
      have h1 := @List.getElem?_eq_getElem _ inputs.val i1.val hlen
      rw [h1]; simp_all
    have h_input_lt : U8x32_as_Nat input.1.bytes < L := by
      apply h_inp_mont_lt i1.val (by omega)
      have hlen : i1.val < inputs.val.length := h_inputs_len ▸ hk_lt
      have h1 := @List.getElem?_eq_getElem _ inputs.val i1.val hlen
      rw [h1]; simp_all
    step as ⟨scratch_val, h_sv_spec⟩
    have h_sv_getElem? : (scratch.val : List _)[i1.val]? = some scratch_val := by
      simp_all
    have h_sv_inv : Scalar52_as_Nat scratch_val ≡ R * PrefixProd vals i1.val [MOD L] :=
      h_scratch_inv i1.val hk_lt scratch_val h_sv_getElem?
    have h_sv_bounds : (∀ k < 5, scratch_val[k]!.val < 2 ^ 52) ∧
        Scalar52_as_Nat scratch_val < L :=
      h_scratch_limbs i1.val hk_lt scratch_val h_sv_getElem?
    step with unpack_spec as ⟨s_val, s_nat_eq, s_limbs⟩
    have h_s_mont : Scalar52_as_Nat s_val ≡ vals i1.val * R [MOD L] := by
      rw [s_nat_eq]; exact h_input_mont
    have h_s_lt : Scalar52_as_Nat s_val < L := by
      rw [s_nat_eq]; exact h_input_lt
    have hacc_limbs62 : ∀ j < 5, acc[j]!.val < 2 ^ 62 :=
      fun j hj => Nat.lt_trans (h_acc_limbs j hj) (by norm_num)
    have hs_limbs62 : ∀ j < 5, s_val[j]!.val < 2 ^ 62 :=
      fun j hj => Nat.lt_trans (s_limbs j hj) (by norm_num)
    have hsv_limbs62 : ∀ j < 5, scratch_val[j]!.val < 2 ^ 62 :=
      fun j hj => Nat.lt_trans (h_sv_bounds.1 j hj) (by norm_num)
    have hLpos : (0 : ℕ) < L := by unfold L; norm_num
    have hLR : L ≤ R := Nat.le_of_lt (by unfold L R; grind)
    have hval_bound_s : Scalar52_as_Nat acc * Scalar52_as_Nat s_val < R * L := by
      cases Nat.eq_zero_or_pos (Scalar52_as_Nat s_val) with
      | inl h =>
        rw [h, Nat.mul_zero]
        exact Nat.mul_pos (Nat.lt_of_lt_of_le hLpos hLR) hLpos
      | inr hpos =>
        calc Scalar52_as_Nat acc * Scalar52_as_Nat s_val
            < L * Scalar52_as_Nat s_val := Nat.mul_lt_mul_of_pos_right h_acc_lt hpos
          _ < L * L := Nat.mul_lt_mul_of_pos_left h_s_lt hLpos
          _ ≤ R * L := Nat.mul_le_mul hLR (le_refl L)
    have hval_bound_sv : Scalar52_as_Nat acc * Scalar52_as_Nat scratch_val < R * L := by
      cases Nat.eq_zero_or_pos (Scalar52_as_Nat scratch_val) with
      | inl h =>
        rw [h, Nat.mul_zero]
        exact Nat.mul_pos (Nat.lt_of_lt_of_le hLpos hLR) hLpos
      | inr hpos =>
        calc Scalar52_as_Nat acc * Scalar52_as_Nat scratch_val
            < L * Scalar52_as_Nat scratch_val := Nat.mul_lt_mul_of_pos_right h_acc_lt hpos
          _ < L * L := Nat.mul_lt_mul_of_pos_left h_sv_bounds.2 hLpos
          _ ≤ R * L := Nat.mul_le_mul hLR (le_refl L)
    step with backend.serial.u64.scalar.Scalar52.montgomery_mul_spec acc s_val
      hacc_limbs62 hs_limbs62 hval_bound_s as ⟨tmp, htmp_mul, htmp_limbs, htmp_lt⟩
    step with backend.serial.u64.scalar.Scalar52.montgomery_mul_spec acc scratch_val
      hacc_limbs62 hsv_limbs62 hval_bound_sv as ⟨s1, hs1_mul, hs1_limbs, hs1_lt⟩
    step with scalar.Scalar52.pack_spec s1 hs1_limbs hs1_lt as ⟨input1, hinput1_mod, _⟩
    have h_acc_inv' : Scalar52_as_Nat tmp * PrefixProd vals i1.val ≡ P [MOD L] :=
      acc_inv_step_loop1 acc tmp s_val vals i1.val P
        (show Scalar52_as_Nat acc * PrefixProd vals (i1.val + 1) ≡ P [MOD L] by
          rw [show i1.val + 1 = i.val from by omega]; exact h_acc_inv)
        h_s_mont htmp_mul
    have h_inv_k : U8x32_as_Nat input1.bytes * vals i1.val ≡ P [MOD L] :=
      inp_inv_step_loop1 acc scratch_val (Scalar52_as_Nat s1) input1.bytes
        vals i1.val P
        (show Scalar52_as_Nat acc * PrefixProd vals (i1.val + 1) ≡ P [MOD L] by
          rw [show i1.val + 1 = i.val from by omega]; exact h_acc_inv)
        h_sv_inv hs1_mul hinput1_mod
    have h_inp_elem : (Slice.set inputs i1 input1).val[i1.val]? = some input1 := by
      simp only [Slice.set_val_eq]
      exact List.getElem?_set_self (h_inputs_len ▸ hk_lt)
    have h_inp_rest : ∀ j, j ≠ i1.val →
        (Slice.set inputs i1 input1).val[j]? = inputs.val[j]? := by
      intro j hj
      simp only [Slice.set_val_eq]
      exact List.getElem?_set_neq inputs.val i1.val j input1 (Or.inl (Ne.symm hj))
    have h_inp_inv' : ∀ j, i1.val ≤ j → j < n.val →
        SliceScalarAt (Slice.set inputs i1 input1) j
          (fun b => U8x32_as_Nat b * vals j ≡ P [MOD L]) :=
      inp_inv_suffix_step inputs _ vals n.val i1.val P input1
        (fun j hj1 hj2 => h_inp_inv j (by omega) hj2)
        h_inv_k h_inp_elem h_inp_rest
    have h_inp_mont' : ∀ j < i1.val,
        SliceScalarAt (Slice.set inputs i1 input1) j
          (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]) :=
      inp_mont_prefix_step inputs _ vals i1.val
        (fun j hj => h_inp_mont j (by omega)) h_inp_rest
    have h_inp_mont_lt' : ∀ j < i1.val,
        SliceScalarAt (Slice.set inputs i1 input1) j
          (fun b => U8x32_as_Nat b < L) :=
      inp_lt_prefix_step inputs _ i1.val L
        (fun j hj => h_inp_mont_lt j (by omega)) h_inp_rest
    simp only [index_mut_back]
    exact spec_mono
      (batch_invert_loop1_spec_strong
        (Slice.set inputs i1 input1) scratch tmp i1 n
        (by omega)
        (by simp [Slice.set_val_eq, List.length_set, h_inputs_len])
        h_scratch_len
        htmp_limbs htmp_lt
        h_scratch_limbs
        vals h_vals_lt P
        h_acc_inv' h_inp_inv' h_inp_mont' h_inp_mont_lt'
        h_scratch_inv)
      (fun result hresult => hresult)
  case isFalse hge =>
    have hi_eq : i.val = 0 := by scalar_tac
    simp only [spec_ok]
    intro j hj
    exact h_inp_inv j (hi_eq ▸ Nat.zero_le j) hj
  termination_by i.val
  decreasing_by scalar_tac

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::batch_invert_loop1`**
• The function always terminates and succeeds when the loop invariants hold.
• For all `j < n`: `U8x32_as_Nat inputs'[j].bytes · vals j ≡ P [MOD L]`.
-/
@[step]
theorem batch_invert_loop1_spec
    (inputs : Slice scalar.Scalar)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52) (i n : Std.Usize)
    (hi : i.val ≤ n.val)
    (h_inputs_len : inputs.val.length = n.val)
    (h_scratch_len : scratch.val.length = n.val)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L)
    (h_scratch_limbs : ∀ j < n.val,
        Vec52At scratch j
          (fun x => (∀ k < 5, x[k]!.val < 2 ^ 52) ∧ Scalar52_as_Nat x < L))
    (vals : ℕ → ℕ)
    (h_vals_lt : ∀ j < n.val, vals j < L)
    (P : ℕ)
    (h_acc_inv : Scalar52_as_Nat acc * PrefixProd vals i.val ≡ P [MOD L])
    (h_inp_inv : ∀ j, i.val ≤ j → j < n.val →
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b * vals j ≡ P [MOD L]))
    (h_inp_mont : ∀ j < i.val,
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b ≡ vals j * R [MOD L]))
    (h_inp_mont_lt : ∀ j < i.val,
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b < L))
    (h_scratch_inv : ∀ j < n.val,
        Vec52At scratch j
          (fun x => Scalar52_as_Nat x ≡ R * PrefixProd vals j [MOD L])) :
    batch_invert_loop1 inputs scratch acc i ⦃ (result : Slice scalar.Scalar) =>
      ∀ j < n.val,
          SliceScalarAt result j (fun b => U8x32_as_Nat b * vals j ≡ P [MOD L]) ⦄ :=
  batch_invert_loop1_spec_strong
    inputs scratch acc i n
    hi h_inputs_len h_scratch_len
    h_acc_limbs h_acc_lt
    h_scratch_limbs
    vals h_vals_lt P
    h_acc_inv h_inp_inv h_inp_mont h_inp_mont_lt
    h_scratch_inv


private lemma R_nz_mod_L : R % L ≠ 0 := by
  unfold R L
  decide

private lemma PrefixProd_nz (vals : ℕ → ℕ) (n : ℕ)
    (h_nz : ∀ j < n, vals j % L ≠ 0) :
    PrefixProd vals n % L ≠ 0 := by
  induction n with
  | zero =>
    simp only [PrefixProd, Finset.range_zero, Finset.prod_empty, ne_eq, Nat.one_mod_eq_zero_iff]
    unfold L
    decide
  | succ k ih =>
    rw [PrefixProd_succ, Nat.mul_mod]
    intro h
    have hL_prime : Nat.Prime L := Fact.out
    have hL_pos : 0 < L := hL_prime.pos
    have hpk : PrefixProd vals k % L ≠ 0 :=
      ih (fun j hj => h_nz j (Nat.lt_succ_of_lt hj))
    have hvk : vals k % L ≠ 0 := h_nz k (Nat.lt_succ_self k)
    have hdvd : L ∣ PrefixProd vals k % L * (vals k % L) :=
      Nat.dvd_of_mod_eq_zero h
    rcases hL_prime.dvd_mul.mp hdvd with h_pk | h_vk
    · exact hpk (Nat.eq_zero_of_dvd_of_lt h_pk (Nat.mod_lt _ hL_pos))
    · exact hvk (Nat.eq_zero_of_dvd_of_lt h_vk (Nat.mod_lt _ hL_pos))

private lemma batch_invert_acc2_inv
    (acc acc2 s2 : backend.serial.u64.scalar.Scalar52)
    (vals : ℕ → ℕ) (n : ℕ)
    (h_acc_prod : Scalar52_as_Nat acc ≡ R * PrefixProd vals n [MOD L])
    (h_mont_inv : Scalar52_as_Nat acc * Scalar52_as_Nat s2 ≡ R * R [MOD L])
    (h_from_mont : Scalar52_as_Nat acc2 * R ≡ Scalar52_as_Nat s2 [MOD L]) :
    Scalar52_as_Nat acc2 * PrefixProd vals n ≡ 1 [MOD L] := by
  apply cancelR; apply cancelR
  simp only [one_mul]
  calc Scalar52_as_Nat acc2 * PrefixProd vals n * R * R
      = (Scalar52_as_Nat acc2 * R) * PrefixProd vals n * R := by ring
    _ ≡ Scalar52_as_Nat s2 * PrefixProd vals n * R [MOD L] :=
          (h_from_mont.mul_right (PrefixProd vals n)).mul_right R
    _ = Scalar52_as_Nat s2 * (R * PrefixProd vals n) := by ring
    _ ≡ Scalar52_as_Nat s2 * Scalar52_as_Nat acc [MOD L] :=
          h_acc_prod.symm.mul_left (Scalar52_as_Nat s2)
    _ = Scalar52_as_Nat acc * Scalar52_as_Nat s2 := by ring
    _ ≡ R * R [MOD L] := h_mont_inv

private lemma from_elem_length
    (one : backend.serial.u64.scalar.Scalar52) (n : Std.Usize)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (h : alloc.vec.from_elem
           backend.serial.u64.scalar.Scalar52.Insts.CoreCloneClone one n = ok scratch) :
    scratch.val.length = n.val := by
  have hclone : backend.serial.u64.scalar.Scalar52.Insts.CoreCloneClone.clone one = ok one :=
    rfl
  have hspec :=
    alloc.vec.from_elem_spec
      backend.serial.u64.scalar.Scalar52.Insts.CoreCloneClone one n hclone
  rw [h] at hspec
  simp only [alloc.vec.Vec.length, spec_ok] at hspec
  exact hspec.2

private theorem batch_invert_loop0_bounds_strong
    (inputs : Slice scalar.Scalar) (n : Std.Usize)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52) (i : Std.Usize)
    (hi : i.val ≤ n.val)
    (h_inputs_len : inputs.val.length = n.val)
    (h_scratch_len : scratch.val.length = n.val)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L)
    (h_scratch_bounds : ∀ j < i.val,
        Vec52At scratch j
          (fun x => (∀ k < 5, x[k]!.val < 2 ^ 52) ∧ Scalar52_as_Nat x < L)) :
    batch_invert_loop0 inputs n scratch acc i ⦃ (result :
        Slice scalar.Scalar × alloc.vec.Vec backend.serial.u64.scalar.Scalar52 ×
        backend.serial.u64.scalar.Scalar52) =>
      ∀ j < n.val,
          Vec52At result.2.1 j
            (fun x => (∀ k < 5, x[k]!.val < 2 ^ 52) ∧ Scalar52_as_Nat x < L) ⦄ := by
  unfold batch_invert_loop0
  split
  case isTrue hlt =>
    have hi_lt : i.val < n.val := by scalar_tac
    have hbound_inputs : i.val < inputs.length := by
      simp only [Slice.length]; omega
    have hbound_scratch : i.val < scratch.length := by
      grind
    simp only [alloc.vec.Vec.index_mut_slice_index]
    haveI : Inhabited scalar.Scalar := ⟨{ bytes := Array.repeat 32#usize 0#u8 }⟩
    haveI : Inhabited backend.serial.u64.scalar.Scalar52 := ⟨Array.repeat 5#usize 0#u64⟩
    step with Slice.index_mut_usize_spec as ⟨input, index_mut_back⟩
    step with alloc.vec.Vec.index_mut_usize_spec scratch i as ⟨_, _, _, h_vec_back⟩
    step
    step
    step
    have hacc_limbs62 : ∀ j < 5, acc[j]!.val < 2 ^ 62 :=
      fun j hj => Nat.lt_trans (h_acc_limbs j hj) (by norm_num)
    have htmp_limbs62 : ∀ j < 5, tmp[j]!.val < 2 ^ 62 := by grind
    have hLpos : (0 : ℕ) < L := by unfold L; norm_num
    have hLR : L ≤ R := Nat.le_of_lt (by unfold L R; grind)
    have hval_bound : Scalar52_as_Nat acc * Scalar52_as_Nat tmp < R * L := by
      cases Nat.eq_zero_or_pos (Scalar52_as_Nat tmp) with
      | inl h =>
        rw [h, Nat.mul_zero]
        exact Nat.mul_pos (Nat.lt_of_lt_of_le hLpos hLR) hLpos
      | inr hpos =>
        calc Scalar52_as_Nat acc * Scalar52_as_Nat tmp
            < L * Scalar52_as_Nat tmp :=
              Nat.mul_lt_mul_of_pos_right h_acc_lt hpos
          _ < L * L := by
              apply Nat.mul_lt_mul_of_pos_left
              all_goals grind
          _ ≤ R * L :=
              Nat.mul_le_mul hLR (le_refl L)
    step
    step as ⟨i1, hi1_val⟩
    have hi1_succ : i1.val = i.val + 1 := by scalar_tac
    have hs1_len : (Slice.set inputs i input1).val.length = n.val := by
      simp [Slice.set_val_eq, List.length_set, h_inputs_len]
    have hscratch1_len : (Slice.set scratch i acc).val.length = n.val := by
      simp [List.length_set, h_scratch_len]
    have h_scratch_new : (Slice.set scratch i acc).val[i.val]? = some acc := by
      simp only [Slice.set_val_eq]
      exact List.getElem?_set_self (h_scratch_len ▸ hi_lt)
    have h_scratch_old : ∀ j, j ≠ i.val →
        (Slice.set scratch i acc).val[j]? = scratch.val[j]? := by
      intro j hj
      simp
      grind
    have h_scratch_bounds' : ∀ j < i1.val,
        Vec52At (Slice.set scratch i acc) j
          (fun x => (∀ k < 5, x[k]!.val < 2 ^ 52) ∧ Scalar52_as_Nat x < L) := by
      rw [hi1_succ]
      intro j hj x hx
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | rfl
      · rw [h_scratch_old j (Nat.ne_of_lt hjlt)] at hx
        exact h_scratch_bounds j hjlt x hx
      · rw [h_scratch_new] at hx
        exact (Option.some.inj hx) ▸ ⟨h_acc_limbs, h_acc_lt⟩
    have hacc1_limbs : ∀ j < 5, acc1[j]!.val < 2 ^ 52 := by grind
    have hacc1_lt : Scalar52_as_Nat acc1 < L := by grind
    simp only [index_mut_back, h_vec_back]
    exact spec_mono
      (batch_invert_loop0_bounds_strong
        (Slice.set inputs i input1) n (Slice.set scratch i acc) acc1 i1
        (by omega)
        hs1_len
        hscratch1_len
        hacc1_limbs hacc1_lt
        h_scratch_bounds')
      (fun result hresult => hresult)
  case isFalse hge =>
    have hi_eq : i.val = n.val := by grind
    simp only [spec_ok]
    intro j hj
    exact h_scratch_bounds j (hi_eq ▸ hj)
  termination_by n.val - i.val
  decreasing_by scalar_tac

private lemma loop0_scratch_limbs
    (inputs : Slice scalar.Scalar) (n : Std.Usize)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L)
    (h_scratch_len : scratch.val.length = n.val)
    (h_inputs_len : inputs.val.length = n.val) :
    batch_invert_loop0 inputs n scratch acc 0#usize ⦃ (result :
        Slice scalar.Scalar × alloc.vec.Vec backend.serial.u64.scalar.Scalar52 ×
        backend.serial.u64.scalar.Scalar52) =>
      ∀ j < n.val,
          Vec52At result.2.1 j
            (fun x => (∀ k < 5, x[k]!.val < 2 ^ 52) ∧ Scalar52_as_Nat x < L) ⦄ :=
  batch_invert_loop0_bounds_strong inputs n scratch acc 0#usize
    (by simp)
    h_inputs_len
    h_scratch_len
    h_acc_limbs h_acc_lt
    (fun j hj => absurd hj (Nat.not_lt_zero j))

private theorem batch_invert_loop0_acc_bounds_strong
    (inputs : Slice scalar.Scalar) (n : Std.Usize)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52) (i : Std.Usize)
    (hi : i.val ≤ n.val)
    (h_inputs_len : inputs.val.length = n.val)
    (h_scratch_len : scratch.val.length = n.val)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L) :
    batch_invert_loop0 inputs n scratch acc i ⦃ (result :
        Slice scalar.Scalar × alloc.vec.Vec backend.serial.u64.scalar.Scalar52 ×
        backend.serial.u64.scalar.Scalar52) =>
      (∀ j < 5, result.2.2[j]!.val < 2 ^ 52) ∧ Scalar52_as_Nat result.2.2 < L ⦄ := by
  unfold batch_invert_loop0
  split
  case isTrue hlt =>
    have hi_lt : i.val < n.val := by scalar_tac
    have hbound_inputs : i.val < inputs.length := by
      simp only [Slice.length]; omega
    have hbound_scratch : i.val < scratch.length := by
      grind
    simp only [alloc.vec.Vec.index_mut_slice_index]
    haveI : Inhabited scalar.Scalar := ⟨{ bytes := Array.repeat 32#usize 0#u8 }⟩
    haveI : Inhabited backend.serial.u64.scalar.Scalar52 := ⟨Array.repeat 5#usize 0#u64⟩
    step with Slice.index_mut_usize_spec as ⟨input, index_mut_back⟩
    step with alloc.vec.Vec.index_mut_usize_spec scratch i as ⟨_, _, _, h_vec_back⟩
    step
    step
    step
    have hacc_limbs62 : ∀ j < 5, acc[j]!.val < 2 ^ 62 :=
      fun j hj => Nat.lt_trans (h_acc_limbs j hj) (by norm_num)
    have htmp_limbs62 : ∀ j < 5, tmp[j]!.val < 2 ^ 62 := by grind
    have hLpos : (0 : ℕ) < L := by unfold L; norm_num
    have hLR : L ≤ R := Nat.le_of_lt (by unfold L R; grind)
    have hval_bound : Scalar52_as_Nat acc * Scalar52_as_Nat tmp < R * L := by
      cases Nat.eq_zero_or_pos (Scalar52_as_Nat tmp) with
      | inl h =>
        rw [h, Nat.mul_zero]
        exact Nat.mul_pos (Nat.lt_of_lt_of_le hLpos hLR) hLpos
      | inr hpos =>
        calc Scalar52_as_Nat acc * Scalar52_as_Nat tmp
            < L * Scalar52_as_Nat tmp :=
              Nat.mul_lt_mul_of_pos_right h_acc_lt hpos
          _ < L * L := by
              apply Nat.mul_lt_mul_of_pos_left
              all_goals grind
          _ ≤ R * L :=
              Nat.mul_le_mul hLR (le_refl L)
    step
    step as ⟨i1, hi1_val⟩
    have hi1_succ : i1.val = i.val + 1 := by scalar_tac
    have hs1_len : (Slice.set inputs i input1).val.length = n.val := by
      simp [Slice.set_val_eq, List.length_set, h_inputs_len]
    have hscratch1_len : (Slice.set scratch i acc).val.length = n.val := by
      simp [List.length_set, h_scratch_len]
    have hacc1_limbs : ∀ j < 5, acc1[j]!.val < 2 ^ 52 := by grind
    have hacc1_lt : Scalar52_as_Nat acc1 < L := by grind
    simp only [index_mut_back, h_vec_back]
    exact spec_mono
      (batch_invert_loop0_acc_bounds_strong
        (Slice.set inputs i input1) n (Slice.set scratch i acc) acc1 i1
        (by omega)
        hs1_len
        hscratch1_len
        hacc1_limbs hacc1_lt)
      (fun result hresult => hresult)
  case isFalse hge =>
    have hi_eq : i.val = n.val := by grind
    simp only [spec_ok]
    exact ⟨h_acc_limbs, h_acc_lt⟩
  termination_by n.val - i.val
  decreasing_by scalar_tac

private lemma loop0_acc_bounds
    (inputs : Slice scalar.Scalar) (n : Std.Usize)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L)
    (h_scratch_len : scratch.val.length = n.val)
    (h_inputs_len : inputs.val.length = n.val) :
    batch_invert_loop0 inputs n scratch acc 0#usize ⦃ (result :
        Slice scalar.Scalar × alloc.vec.Vec backend.serial.u64.scalar.Scalar52 ×
        backend.serial.u64.scalar.Scalar52) =>
      (∀ j < 5, result.2.2[j]!.val < 2 ^ 52) ∧ Scalar52_as_Nat result.2.2 < L ⦄ :=
  batch_invert_loop0_acc_bounds_strong inputs n scratch acc 0#usize
    (by simp)
    h_inputs_len
    h_scratch_len
    h_acc_limbs h_acc_lt

private theorem batch_invert_loop0_inputs_lt_strong
    (inputs : Slice scalar.Scalar) (n : Std.Usize)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52) (i : Std.Usize)
    (hi : i.val ≤ n.val)
    (h_inputs_len : inputs.val.length = n.val)
    (h_scratch_len : scratch.val.length = n.val)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L)
    (h_inp_lt : ∀ j < i.val, SliceScalarAt inputs j (fun b => U8x32_as_Nat b < L)) :
    batch_invert_loop0 inputs n scratch acc i ⦃ (result :
        Slice scalar.Scalar × alloc.vec.Vec backend.serial.u64.scalar.Scalar52 ×
        backend.serial.u64.scalar.Scalar52) =>
      ∀ j < n.val, SliceScalarAt result.1 j (fun b => U8x32_as_Nat b < L) ⦄ := by
  unfold batch_invert_loop0
  split
  case isTrue hlt =>
    have hi_lt : i.val < n.val := by scalar_tac
    have hbound_inputs : i.val < inputs.length := by
      simp only [Slice.length]; omega
    have hbound_scratch : i.val < scratch.length := by
      grind
    simp only [alloc.vec.Vec.index_mut_slice_index]
    haveI : Inhabited scalar.Scalar := ⟨{ bytes := Array.repeat 32#usize 0#u8 }⟩
    haveI : Inhabited backend.serial.u64.scalar.Scalar52 := ⟨Array.repeat 5#usize 0#u64⟩
    step with Slice.index_mut_usize_spec as ⟨input, index_mut_back⟩
    step with alloc.vec.Vec.index_mut_usize_spec scratch i as ⟨_, _, _, h_vec_back⟩
    step
    step
    step
    have hacc_limbs62 : ∀ j < 5, acc[j]!.val < 2 ^ 62 :=
      fun j hj => Nat.lt_trans (h_acc_limbs j hj) (by norm_num)
    have htmp_limbs62 : ∀ j < 5, tmp[j]!.val < 2 ^ 62 := by grind
    have hLpos : (0 : ℕ) < L := by unfold L; norm_num
    have hLR : L ≤ R := Nat.le_of_lt (by unfold L R; grind)
    have hval_bound : Scalar52_as_Nat acc * Scalar52_as_Nat tmp < R * L := by
      cases Nat.eq_zero_or_pos (Scalar52_as_Nat tmp) with
      | inl h =>
        rw [h, Nat.mul_zero]
        exact Nat.mul_pos (Nat.lt_of_lt_of_le hLpos hLR) hLpos
      | inr hpos =>
        calc Scalar52_as_Nat acc * Scalar52_as_Nat tmp
            < L * Scalar52_as_Nat tmp :=
              Nat.mul_lt_mul_of_pos_right h_acc_lt hpos
          _ < L * L := by
              apply Nat.mul_lt_mul_of_pos_left
              all_goals grind
          _ ≤ R * L :=
              Nat.mul_le_mul hLR (le_refl L)
    step
    step as ⟨i1, hi1_val⟩
    have hi1_succ : i1.val = i.val + 1 := by scalar_tac
    have hs1_len : (Slice.set inputs i input1).val.length = n.val := by
      simp [Slice.set_val_eq, List.length_set, h_inputs_len]
    have hscratch1_len : (Slice.set scratch i acc).val.length = n.val := by
      simp [List.length_set, h_scratch_len]
    have h_inp_elem : (Slice.set inputs i input1).val[i.val]? = some input1 := by
      simp only [Slice.set_val_eq]
      exact List.getElem?_set_self (h_inputs_len ▸ hi_lt)
    have h_inp_rest : ∀ j, j ≠ i.val →
        (Slice.set inputs i input1).val[j]? = inputs.val[j]? := by
      intro j hj; simp; grind
    have h_inp_lt' : ∀ j < i1.val,
        SliceScalarAt (Slice.set inputs i input1) j (fun b => U8x32_as_Nat b < L) := by
      rw [hi1_succ]
      intro j hj x hx
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | rfl
      · rw [h_inp_rest j (Nat.ne_of_lt hjlt)] at hx
        exact h_inp_lt j hjlt x hx
      · rw [h_inp_elem] at hx
        exact (Option.some.inj hx) ▸ input1_post2
    have hacc1_limbs : ∀ j < 5, acc1[j]!.val < 2 ^ 52 := by grind
    have hacc1_lt : Scalar52_as_Nat acc1 < L := by grind
    simp only [index_mut_back, h_vec_back]
    exact spec_mono
      (batch_invert_loop0_inputs_lt_strong
        (Slice.set inputs i input1) n (Slice.set scratch i acc) acc1 i1
        (by omega)
        hs1_len
        hscratch1_len
        hacc1_limbs hacc1_lt
        h_inp_lt')
      (fun result hresult => hresult)
  case isFalse hge =>
    have hi_eq : i.val = n.val := by grind
    simp only [spec_ok]
    intro j hj
    exact h_inp_lt j (hi_eq ▸ hj)
  termination_by n.val - i.val
  decreasing_by scalar_tac

private lemma loop0_inputs_lt
    (inputs : Slice scalar.Scalar) (n : Std.Usize)
    (scratch : alloc.vec.Vec backend.serial.u64.scalar.Scalar52)
    (acc : backend.serial.u64.scalar.Scalar52)
    (h_acc_limbs : ∀ j < 5, acc[j]!.val < 2 ^ 52)
    (h_acc_lt : Scalar52_as_Nat acc < L)
    (h_scratch_len : scratch.val.length = n.val)
    (h_inputs_len : inputs.val.length = n.val) :
    batch_invert_loop0 inputs n scratch acc 0#usize ⦃ (result :
        Slice scalar.Scalar × alloc.vec.Vec backend.serial.u64.scalar.Scalar52 ×
        backend.serial.u64.scalar.Scalar52) =>
      ∀ j < n.val, SliceScalarAt result.1 j (fun b => U8x32_as_Nat b < L) ⦄ :=
  batch_invert_loop0_inputs_lt_strong inputs n scratch acc 0#usize
    (by simp)
    h_inputs_len
    h_scratch_len
    h_acc_limbs h_acc_lt
    (fun j hj => absurd hj (Nat.not_lt_zero j))

private theorem spec_and {α} {m : Result α} {P Q : α → Prop}
    (hp : m ⦃ P ⦄) (hq : m ⦃ Q ⦄) : m ⦃ fun r => P r ∧ Q r ⦄ := by
  cases m with
  | ok v => exact ⟨hp, hq⟩
  | fail e => exact hp
  | div => exact hp

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::batch_invert`**
• The function always succeeds (no panic) provided all inputs are non-zero modulo `L`.
• `U8x32_as_Nat ret.bytes · PrefixProd vals n ≡ 1  [MOD L]`
  (`ret` is the multiplicative inverse of the full product of the original inputs).
• `∀ j < n, U8x32_as_Nat inputs2[j].bytes · vals j ≡ 1  [MOD L]`
  (each entry of `inputs2` holds the multiplicative inverse of the corresponding original input).
-/
@[step]
theorem batch_invert_spec
    (inputs : Slice scalar.Scalar)
    (vals : ℕ → ℕ)
    (h_vals_lt : ∀ j < inputs.val.length, vals j < L)
    (h_vals_nz : ∀ j < inputs.val.length, vals j % L ≠ 0)
    (h_vals_def : ∀ j < inputs.val.length,
        SliceScalarAt inputs j (fun b => U8x32_as_Nat b = vals j)) :
    batch_invert inputs ⦃ (result : scalar.Scalar × Slice scalar.Scalar) =>
      U8x32_as_Nat result.1.bytes * PrefixProd vals inputs.val.length ≡ 1 [MOD L] ∧
      ∀ j < inputs.val.length,
          SliceScalarAt result.2 j
            (fun b => U8x32_as_Nat b * vals j ≡ 1 [MOD L]) ⦄ := by
  simp only [batch_invert]
  have hn_val : (Slice.len inputs).val = inputs.val.length := by
    simp [Slice.len]
  let* ⟨s, hs_nat, hs_limbs⟩ ← unpack_spec
  have hs_eq_one : Scalar52_as_Nat s = 1 := by
    rw [hs_nat]; unfold ONE; decide
  let* ⟨one, hone_mod, hone_limbs, hone_lt⟩ ←
    backend.serial.u64.scalar.Scalar52.as_montgomery_spec s hs_limbs
  have hone_R : Scalar52_as_Nat one ≡ R [MOD L] := by
    rwa [hs_eq_one, Nat.one_mul] at hone_mod
  step
  · rfl
  have h_scratch_len : scratch.val.length = (Slice.len inputs).val := scratch_post2
  let* ⟨acc, hacc_mod, hacc_limbs, hacc_lt⟩ ←
    backend.serial.u64.scalar.Scalar52.as_montgomery_spec s hs_limbs
  have hacc_R : Scalar52_as_Nat acc ≡ R [MOD L] := by
    rwa [hs_eq_one, Nat.one_mul] at hacc_mod
  have h_inputs_len : inputs.val.length = (Slice.len inputs).val := hn_val.symm
  have h_loop0_combined :=
    spec_and
      (batch_invert_loop0_spec inputs (Slice.len inputs) scratch acc 0#usize
        (by simp)
        h_inputs_len
        h_scratch_len
        hacc_limbs hacc_lt
        R vals
        (by rwa [hn_val])
        (by simp only [UScalar.ofNatCore_val_eq, PrefixProd_zero, mul_one]; exact hacc_R)
        (fun j hj => absurd hj (Nat.not_lt_zero j))
        (fun j hj => absurd hj (Nat.not_lt_zero j))
        (fun j _ hj x hx => h_vals_def j (by rwa [← hn_val]) x hx))
      (spec_and
        (loop0_inputs_lt inputs (Slice.len inputs) scratch acc
          hacc_limbs hacc_lt h_scratch_len h_inputs_len)
        (loop0_scratch_limbs inputs (Slice.len inputs) scratch acc
          hacc_limbs hacc_lt h_scratch_len h_inputs_len))
  step with h_loop0_combined
    as ⟨hacc1_res, hacc1_inv, hscratch1_inv, hinp1_mont, hinp1_mont1, hinp1_mont2,
      hinputs1_len_post, hscratch1_len_post, hinp1_mont_lt_pre, hscratch1_limbs_pre⟩
  set acc1 := hacc1_res.2.2 with hacc1
  have hacc1_limbs : ∀ j < 5, acc1[j]!.val < 2 ^ 52 := hinp1_mont1
  have hacc1_lt : Scalar52_as_Nat acc1 < L := hinp1_mont2
  step
  step
  step
  · rw [b_post]
    intro h_eq
    have h_zero : U8x32_as_Nat s1.bytes = 0 :=
      (U8x32_as_Nat_eq_zero_iff_ZERO s1).mpr (Scalar_ext s1 ZERO h_eq)
    have h_cong : (0 : ℕ) ≡ R * PrefixProd vals (Slice.len inputs).val [MOD L] := by
      have h := s1_post1.trans hacc1_inv
      rw [h_zero] at h
      exact h
    have h_prod_nz : R * PrefixProd vals (Slice.len inputs).val % L ≠ 0 := by
      rw [Nat.mul_mod]
      intro h
      have hL : Nat.Prime L := Fact.out
      have hdvd : L ∣ R % L * (PrefixProd vals (Slice.len inputs).val % L) :=
        Nat.dvd_of_mod_eq_zero h
      rcases hL.dvd_mul.mp hdvd with hR | hPP
      · exact R_nz_mod_L (Nat.eq_zero_of_dvd_of_lt hR (Nat.mod_lt _ hL.pos))
      · exact (PrefixProd_nz vals (Slice.len inputs).val
                (fun j hj => h_vals_nz j (by grind)))
                (Nat.eq_zero_of_dvd_of_lt hPP (Nat.mod_lt _ hL.pos))
    have h_rp_zero : R * PrefixProd vals (Slice.len inputs).val % L = 0 := by
      have h := h_cong.symm
      unfold Nat.ModEq at h
      simp only [Nat.zero_mod] at h
      exact h
    exact h_prod_nz h_rp_zero
  step
  · intro h_zero
    have h_rp : Scalar52_as_Nat acc1 % L =
        (R * PrefixProd vals (Slice.len inputs).val) % L := hacc1_inv
    rw [h_zero] at h_rp
    have h_prod_nz : R * PrefixProd vals (Slice.len inputs).val % L ≠ 0 := by
      rw [Nat.mul_mod]
      intro h
      have hL_prime : Nat.Prime L := Fact.out
      have hdvd : L ∣ R % L * (PrefixProd vals (Slice.len inputs).val % L) :=
        Nat.dvd_of_mod_eq_zero h
      rcases hL_prime.dvd_mul.mp hdvd with hR | hPP
      · exact R_nz_mod_L (Nat.eq_zero_of_dvd_of_lt hR (Nat.mod_lt _ hL_prime.pos))
      · exact (PrefixProd_nz vals (Slice.len inputs).val
                (fun j hj => h_vals_nz j (by grind)))
                (Nat.eq_zero_of_dvd_of_lt hPP (Nat.mod_lt _ hL_prime.pos))
    exact h_prod_nz h_rp.symm
  · have hLpos : (0 : ℕ) < L := by unfold L; norm_num
    have hLR : L ≤ R := Nat.le_of_lt (by unfold L R; grind)
    cases Nat.eq_zero_or_pos (Scalar52_as_Nat acc1) with
    | inl h =>
      rw [h, Nat.zero_mul]
      exact Nat.mul_pos (Nat.lt_of_lt_of_le hLpos hLR) hLpos
    | inr hpos =>
      calc Scalar52_as_Nat acc1 * Scalar52_as_Nat acc1
          < L * Scalar52_as_Nat acc1 :=
            Nat.mul_lt_mul_of_pos_right hacc1_lt hpos
        _ < L * L :=
            Nat.mul_lt_mul_of_pos_left hacc1_lt hLpos
        _ ≤ R * L :=
            Nat.mul_le_mul hLR (le_refl L)
  have hs2_limbs62 : ∀ j < 5, s2[j]!.val < 2 ^ 62 := by
    grind
  step
  have hacc2_R : Scalar52_as_Nat acc2 * R ≡ Scalar52_as_Nat s2 [MOD L] := by
    unfold Nat.ModEq
    grind
  have hacc2_limbs : ∀ j < 5, acc2[j]!.val < 2 ^ 52 := by grind
  have hacc2_lt : Scalar52_as_Nat acc2 < L := by grind
  -- Key: acc2 is the inverse of PrefixProd vals n modulo L
  have hacc2_inv : Scalar52_as_Nat acc2 * PrefixProd vals (Slice.len inputs).val ≡ 1 [MOD L] := by
    have hmontinv : Scalar52_as_Nat acc1 * Scalar52_as_Nat s2 ≡ R * R [MOD L] := by
      unfold Nat.ModEq
      grind
    exact batch_invert_acc2_inv acc1 acc2 s2 vals (Slice.len inputs).val
      hacc1_inv hmontinv hacc2_R
  step
  have hret_inv : U8x32_as_Nat ret.bytes * PrefixProd vals inputs.val.length ≡ 1 [MOD L] := by
    rw [hn_val] at hacc2_inv
    exact (ret_post1.mul_right (PrefixProd vals inputs.val.length)).trans hacc2_inv
  set inputs1:=hacc1_res.1 with hinputs1
  set scratch1:= hacc1_res.2.1  with hscratch1
  have hinp1_mont_lt : ∀ j < (Slice.len inputs).val,
      SliceScalarAt inputs1 j (fun b => U8x32_as_Nat b < L) := hinp1_mont_lt_pre
  have hscratch1_limbs : ∀ j < (Slice.len inputs).val,
      Vec52At scratch1 j
        (fun x => (∀ k < 5, x[k]!.val < 2 ^ 52) ∧ Scalar52_as_Nat x < L) := hscratch1_limbs_pre
  step with batch_invert_loop1_spec
    inputs1 scratch1 acc2 (Slice.len inputs) (Slice.len inputs)
    (le_refl _)
    hinputs1_len_post
    hscratch1_len_post
    hacc2_limbs hacc2_lt
    hscratch1_limbs
    vals
    (by rwa [hn_val])
    1
    hacc2_inv
    (fun j hj1 hj2 => by omega)
    (by rwa [hn_val])
    hinp1_mont_lt
    (fun j hj x hx => by
      exact hscratch1_inv j hj x hx)
    as ⟨hinputs2_inv⟩
  step*

end curve25519_dalek.scalar.Scalar
