/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.Basic

/-! # List Bool bit manipulation infrastructure

Definitions and lemmas for reasoning about bit-level operations using `List Bool`. The key idea is
that bitwise operations like shifts and masks correspond to simple list operations (`List.drop`,
`List.take`, `List.extract`).

All bit lists are **LSB-first**: the head of the list is bit 0 (least significant).
-/

open Aeneas Aeneas.Std

attribute [grind =] Nat.add_mod Nat.mul_mod_mul_left Nat.mod_eq_of_lt
attribute [grind .] Nat.mod_lt

namespace BitList
open List

/-! ## Core definitions -/

/-- Interpret a list of booleans as a natural number (LSB-first).
    `toNat [true, false, true] = 1 + 0 + 4 = 5` -/
def toNat : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * toNat bs

/-- Convert a natural number to a fixed-width bit list (LSB-first). `ofNat w n` encodes `n` as a bit
list of width `w`. E.g., `ofNat 4 5 = [true, false, true, false]`. -/
def ofNat : Nat → Nat → List Bool
  | 0, _ => []
  | w + 1, n => (n % 2 == 1) :: ofNat w (n / 2)

/-- Two bit lists are equivalent if they agree at every position, treating out-of-bounds positions
as `false`. I.e., same numeric value, possibly different widths. -/
def Equiv (bs₁ bs₂ : List Bool) : Prop :=
  ∀ i : Nat, bs₁.getD i false = bs₂.getD i false

scoped infix:50 " ≈ₗ " => BitList.Equiv

/-! ## Scalar type conversions -/

/-- 8-bit LSB-first representation of a U8 value. -/
def ofU8 (x : U8) : List Bool := ofNat 8 x.val

/-- 64-bit LSB-first representation of a U64 value. -/
def ofU64 (x : U64) : List Bool := ofNat 64 x.val

/-- Convert a list of bytes to a flat bit list (LSB-first within each byte, bytes in list order). -/
def ofByteList (bytes : List U8) : List Bool :=
  (bytes.map ofU8).flatten

/-- Convert a 32-byte array to a 256-bit list. -/
def ofByteArray (arr : Array U8 32#usize) : List Bool :=
  ofByteList arr.val

/-! ## Equiv: basic properties -/

variable {bs₁ bs₂ bs₃ : List Bool}

@[simp, refl]
theorem Equiv.refl (bs : List Bool) : bs ≈ₗ bs :=
  fun _ => rfl

@[grind →]
theorem Equiv.symm (h : bs₁ ≈ₗ bs₂) : bs₂ ≈ₗ bs₁ :=
  fun i => (h i).symm

@[grind →]
theorem Equiv.trans (h₁ : bs₁ ≈ₗ bs₂) (h₂ : bs₂ ≈ₗ bs₃) : bs₁ ≈ₗ bs₃ :=
  fun i => (h₁ i).trans (h₂ i)

/-- Appending `false` bits does not change equivalence. -/
@[grind =]
theorem Equiv.append_false (bs : List Bool) (n : Nat) :
    bs ++ replicate n false ≈ₗ bs := by
  intro i; by_cases i < bs.length <;> grind

/-- Equiv implies the same numeric value. -/
private theorem getD_drop_one (bs : List Bool) (i : Nat) :
    (bs.drop 1).getD i false = bs.getD (i + 1) false := by
  cases bs with
  | nil => simp
  | cons _ _ => simp

private theorem toNat_eq_toNat_of_equiv_aux (n : Nat) :
    ∀ (bs₁ bs₂ : List Bool), bs₁.length ≤ n → bs₂.length ≤ n →
    (bs₁ ≈ₗ bs₂) → toNat bs₁ = toNat bs₂ := by
  induction n with
  | zero => grind
  | succ n ih =>
    intro bs₁ bs₂ h1 h2 heq
    have step : ∀ bs : List Bool,
        toNat bs = (bs.getD 0 false).toNat + 2 * toNat (bs.drop 1) := by
      intro bs; cases bs <;> simp [toNat, getD]
    rw [step bs₁, step bs₂, heq 0]
    have : toNat (bs₁.drop 1) = toNat (bs₂.drop 1) := by
      apply ih
      · grind [length_drop]
      · grind [length_drop]
      · intro i; simp only [getD_drop_one]; exact heq (i + 1)
    omega

@[grind →]
theorem Equiv.toNat_eq (h : bs₁ ≈ₗ bs₂) : toNat bs₁ = toNat bs₂ :=
  toNat_eq_toNat_of_equiv_aux (bs₁.length + bs₂.length) bs₁ bs₂ (by omega) (by omega) h

/-- Equiv is preserved by `List.take` on both sides. -/
private theorem getD_take (bs : List Bool) (n i : Nat) :
    (bs.take n).getD i false = if i < n then bs.getD i false else false := by
  by_cases hi : i < n <;> simp [hi]

theorem Equiv.take (h : bs₁ ≈ₗ bs₂) (n : Nat) :
    bs₁.take n ≈ₗ bs₂.take n := by
  intro i
  simp only [getD_take]
  split <;> [exact h i; rfl]

/-- Equiv is preserved by `List.drop` on both sides. -/
private theorem getD_drop (bs : List Bool) (n i : Nat) :
    (bs.drop n).getD i false = bs.getD (n + i) false := by
  simp only [getD_eq_getElem?_getD, getElem?_drop]

theorem Equiv.drop (h : bs₁ ≈ₗ bs₂) (n : Nat) :
    bs₁.drop n ≈ₗ bs₂.drop n := by
  intro i
  simp only [getD_drop]
  exact h (n + i)

/-- Equiv is preserved by `List.extract` on both sides. -/
theorem Equiv.extract (h : bs₁ ≈ₗ bs₂) (start stop : Nat) :
    bs₁.extract start stop ≈ₗ bs₂.extract start stop := by
  simp only [extract_eq_drop_take]
  exact (h.drop start).take (stop - start)

/-! ### Grind support for chaining Equiv through take/drop -/

attribute [grind =] List.drop_take List.drop_drop List.take_take

@[grind →]
theorem Equiv.trans_take {m n : Nat}
    (h1 : bs₁ ≈ₗ bs₂.take m) (h2 : bs₂ ≈ₗ bs₃.take n) :
    bs₁ ≈ₗ bs₃.take (min m n) :=
  h1.trans ((h2.take m).trans (by simp [List.take_take]))

@[grind →]
theorem Equiv.trans_drop {m : Nat}
    (h1 : bs₁ ≈ₗ bs₂.drop m) (h2 : bs₂ ≈ₗ bs₃) :
    bs₁ ≈ₗ bs₃.drop m :=
  h1.trans (h2.drop m)

@[grind →]
theorem Equiv.trans_take_drop {m n : Nat}
    (h1 : bs₁ ≈ₗ bs₂.take m) (h2 : bs₂ ≈ₗ bs₃.drop n) :
    bs₁ ≈ₗ (bs₃.drop n).take m :=
  h1.trans (h2.take m)

/-! ## Length lemmas -/

/-- `ofNat w n` always produces exactly `w` bits. -/
theorem ofNat_length (w n : Nat) : (ofNat w n).length = w := by
  induction w generalizing n with
  | zero => simp [ofNat]
  | succ w ih => simp [ofNat, ih]

theorem ofU8_length (x : U8) : (ofU8 x).length = 8 :=
  ofNat_length 8 x.val

theorem ofU64_length (x : U64) : (ofU64 x).length = 64 :=
  ofNat_length 64 x.val

theorem ofByteList_length (bytes : List U8) :
    (ofByteList bytes).length = 8 * bytes.length := by
  induction bytes with
  | nil => simp [ofByteList]
  | cons x xs ih =>
    unfold ofByteList
    simp only [map_cons, flatten_cons, length_append, ofU8_length]
    change 8 + (ofByteList xs).length = 8 * (xs.length + 1)
    rw [ih]; ring

theorem ofByteArray_length (arr : Array U8 32#usize) :
    (ofByteArray arr).length = 256 := by
  simp [ofByteArray, ofByteList_length, arr.property]

/-! ## Pure List Bool lemmas: `ofNat` interacts with list operations

These are the primary lemmas, stated as equalities between `List Bool` values. -/

/-- Taking fewer bits gives the narrower representation (mask is take). -/
theorem ofNat_take (k w : Nat) (n : Nat) (hkw : k ≤ w) :
    (ofNat w n).take k = ofNat k n := by
  induction k generalizing w n with
  | zero => simp [ofNat]
  | succ k ih =>
    match w, hkw with
    | w + 1, hkw => grind [ofNat]

/-- Dropping bits gives the shifted representation (shift is drop). -/
theorem ofNat_drop (k w : Nat) (n : Nat) (hkw : k ≤ w) :
    (ofNat w n).drop k = ofNat (w - k) (n / 2 ^ k) := by
  induction k generalizing w n with
  | zero => simp
  | succ k ih =>
    match w, hkw with
    | w + 1, hkw =>
      simp only [ofNat, drop_succ_cons]
      rw [ih w (n / 2) (by omega)]
      grind [Nat.pow_succ', Nat.div_div_eq_div_mul]

/-- Extracting a range of bits gives the shifted, narrower representation. -/
theorem ofNat_extract (w start len : Nat) (n : Nat) (h : start + len ≤ w) :
    (ofNat w n).extract start (start + len) = ofNat len (n / 2 ^ start) := by
  simp only [extract_eq_drop_take]
  rw [ofNat_drop start w n (by omega)]
  rw [show start + len - start = len from by omega]
  exact ofNat_take len (w - start) (n / 2 ^ start) (by omega)

/-- Splitting a bit list gives two shorter bit lists. -/
theorem ofNat_split (w₁ w₂ : Nat) (n : Nat) :
    ofNat (w₁ + w₂) n = ofNat w₁ n ++ ofNat w₂ (n / 2 ^ w₁) := by
  induction w₁ generalizing n with
  | zero => simp [ofNat]
  | succ w₁ ih =>
    have : w₁ + 1 + w₂ = (w₁ + w₂) + 1 := by omega
    grind [ofNat, Nat.pow_succ', Nat.div_div_eq_div_mul]

/-- `ofNat w` ignores bits above position w: `ofNat w (n % 2^w) = ofNat w n`. -/
theorem ofNat_mod (w n : Nat) :
    ofNat w (n % 2 ^ w) = ofNat w n := by
  induction w generalizing n with
  | zero => simp [ofNat]
  | succ w ih =>
    have : n % 2 ^ (w + 1) % 2 = n % 2 :=
      Nat.mod_mod_of_dvd n (by rw [Nat.pow_succ']; exact dvd_mul_right 2 (2 ^ w))
    have : n % (2 * 2 ^ w) / 2 = n / 2 % 2 ^ w :=
      Nat.mod_mul_right_div_self n 2 (2 ^ w)
    grind [ofNat]

/-- A wider representation is Equiv to a narrower one when the value fits. -/
private theorem ofNat_zero (w : Nat) : ofNat w 0 = replicate w false := by
  induction w with
  | zero => simp [ofNat]
  | succ w ih => simp [ofNat, ih, replicate_succ]

theorem ofNat_equiv_of_lt (k w : Nat) (n : Nat) (hkw : k ≤ w) (hn : n < 2 ^ k) :
    ofNat w n ≈ₗ ofNat k n := by
  have : w = k + (w - k) := by omega
  have : n / 2 ^ k = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hn)
  grind [ofNat_split, ofNat_zero, Equiv.append_false]

/-! ## Composing extracts -/

/-- Extracting from an extract composes: takes the sub-subrange. -/
theorem extract_extract {α : Type} (l : List α) (a b c d : Nat) (hcd : c + d ≤ b - a) :
    (l.extract a b).extract c (c + d) = l.extract (a + c) (a + c + d) := by
  simp only [extract_eq_drop_take, drop_take, drop_drop]
  grind

/-! ## Byte list decomposition into bits -/

/-- The bits of a cons byte list are the head byte's bits followed by the tail's. -/
theorem ofByteList_cons (x : U8) (xs : List U8) :
    ofByteList (x :: xs) = ofU8 x ++ ofByteList xs := by
  simp [ofByteList]

/-- Extracting 8-aligned bits from a byte list equal to extracting the corresponding bytes. -/
private theorem flatten_drop_uniform {α : Type} (xss : List (List α)) (k i : Nat)
    (hunif : ∀ xs ∈ xss, xs.length = k) :
    (xss.flatten).drop (k * i) = (xss.drop i).flatten := by
  induction i generalizing xss with
  | zero => simp
  | succ i ih =>
    cases xss with
    | nil => simp
    | cons xs xss =>
      simp only [flatten_cons, drop_succ_cons]
      have : xs.length = k := hunif xs (by simp)
      have : k * (i + 1) = xs.length + k * i := by rw [this]; ring
      rw [this, drop_append, drop_eq_nil_of_le (by omega)]
      simpa [add_tsub_cancel_left, nil_append] using
        ih xss (fun ys hy => hunif ys (by simp [hy]))

private theorem flatten_take_uniform {α : Type} (xss : List (List α)) (k n : Nat)
    (hunif : ∀ xs ∈ xss, xs.length = k) :
    (xss.flatten).take (k * n) = (xss.take n).flatten := by
  induction n generalizing xss with
  | zero => simp
  | succ n ih =>
    cases xss with
    | nil => simp
    | cons xs xss =>
      have : xs.length = k := hunif xs (by simp)
      have : k * (n + 1) = xs.length + k * n := by rw [this]; ring
      simpa [this, take_append, take_of_length_le] using
        ih xss (fun ys hy => hunif ys (by simp [hy]))

theorem ofByteList_extract (bytes : List U8) (i j : Nat) (_ : j ≤ bytes.length) :
    (ofByteList bytes).extract (8 * i) (8 * j) = ofByteList (bytes.extract i j) := by
  simp only [extract_eq_drop_take, ofByteList]
  have hunif : ∀ xs ∈ (bytes.map ofU8), xs.length = 8 := by
    intro _ hxs
    rw [mem_map] at hxs
    obtain ⟨x, _, rfl⟩ := hxs
    exact ofU8_length x
  rw [show 8 * j - 8 * i = 8 * (j - i) from by omega]
  rw [flatten_drop_uniform _ 8 i hunif]
  rw [flatten_take_uniform _ 8 (j - i) (by intro xs hxs; exact hunif xs (mem_of_mem_drop hxs))]
  grind [map_drop, map_take]

/-! ## Round-trip and bridge lemmas (connecting to Nat) -/

/-- Converting to bits and back recovers the original value. -/
private theorem beq_one_toNat (n : Nat) : (n % 2 == 1).toNat + 2 * (n / 2) = n := by
  have h1 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases h1 with h | h <;> simp [h, Bool.toNat] <;> omega

theorem toNat_ofNat (w n : Nat) (h : n < 2 ^ w) : toNat (ofNat w n) = n := by
  induction w generalizing n with
  | zero => simp [ofNat, toNat]; omega
  | succ w ih =>
    have hd : n / 2 < 2 ^ w := by grind
    simp only [ofNat, toNat, ih _ hd]
    exact beq_one_toNat n

theorem toNat_ofU8 (x : U8) : toNat (ofU8 x) = x.val :=
  toNat_ofNat 8 x.val x.hmax

theorem toNat_ofU64 (x : U64) : toNat (ofU64 x) = x.val :=
  toNat_ofNat 64 x.val x.hmax

/-- If a bit list has length w, converting to Nat and back gives the same list. -/
theorem ofNat_toNat (bs : List Bool) :
    ofNat bs.length (toNat bs) = bs := by
  induction bs with
  | nil => simp [ofNat, toNat]
  | cons b bs ih =>
    simp only [length_cons, toNat, ofNat]
    congr 1
    · cases b <;> simp [Bool.toNat]
    · have : (b.toNat + 2 * toNat bs) / 2 = toNat bs := by
        cases b <;> simp [Bool.toNat]; omega
      rw [this, ih]

/-- A bit list's value is bounded by `2^length`. -/
theorem toNat_lt_pow (bs : List Bool) : toNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [toNat]
  | cons b bs ih =>
    have : b.toNat ≤ 1 := Bool.toNat_le b
    grind [toNat, Nat.pow_succ']

/-- Appending two bit lists adds their values with the appropriate shift. -/
theorem toNat_append (bs₁ bs₂ : List Bool) :
    toNat (bs₁ ++ bs₂) = toNat bs₁ + toNat bs₂ * 2 ^ bs₁.length := by
  induction bs₁ with
  | nil => simp [toNat]
  | cons _ _ _ => grind [toNat, Nat.pow_succ']

/-- Taking k bits gives the value mod 2^k. -/
theorem toNat_take (k : Nat) (bs : List Bool) :
    toNat (bs.take k) = toNat bs % 2 ^ k := by
  induction k generalizing bs with
  | zero => simp [toNat, Nat.mod_one]
  | succ k ih =>
    cases bs with
    | nil => simp [toNat]
    | cons b bs =>
      have := Bool.toNat_le b
      grind [toNat]

/-- Dropping k bits gives the value divided by 2^k. -/
private theorem add_mul_two_div (a m : Nat) (ha : a < 2) :
    (a + 2 * m) / 2 = m := by omega

theorem toNat_drop (k : Nat) (bs : List Bool) :
    toNat (bs.drop k) = toNat bs / 2 ^ k := by
  induction k generalizing bs with
  | zero => simp
  | succ k ih =>
    cases bs with
    | nil => simp [toNat]
    | cons b bs =>
      simp only [drop_succ_cons, toNat, Nat.pow_succ']
      rw [ih bs]
      rw [← Nat.div_div_eq_div_mul]
      congr 1
      exact (add_mul_two_div b.toNat (toNat bs) (by have := Bool.toNat_le b; omega)).symm

/-- The value of a byte list's bits equals the base-256 interpretation. -/
theorem toNat_ofByteList (bytes : List U8) :
    toNat (ofByteList bytes) = Nat.ofDigits 256 (bytes.map (·.val)) := by
  induction bytes with
  | nil => simp [ofByteList, toNat]
  | cons x xs ih =>
    simp only [ofByteList_cons, toNat_append, toNat_ofU8, ofU8_length,
      map_cons, Nat.ofDigits, ih]
    push_cast; ring

/-- `Nat.ofDigits 256` on a byte list equals the corresponding `Finset.sum`. -/
lemma ofDigits_map_val_eq_sum (bytes : List U8) :
    Nat.ofDigits 256 (bytes.map (·.val)) =
      ∑ j ∈ Finset.range bytes.length, bytes[j]!.val * 256 ^ j := by
  induction bytes with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, length_cons]
    rw [Finset.sum_range_succ']
    simp only [Nat.pow_zero, Nat.mul_one, getElem!_cons_zero]
    rw [Nat.ofDigits]
    rw [ih, Finset.mul_sum]
    rw [Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [getElem!_cons_succ]
    ring

/-- The value of a 32-byte array's bits equals U8x32_as_Nat. -/
theorem toNat_ofByteArray (arr : Array U8 32#usize) :
    toNat (ofByteArray arr) = U8x32_as_Nat arr := by
  rw [ofByteArray, toNat_ofByteList, ofDigits_map_val_eq_sum]
  unfold U8x32_as_Nat
  rw [show arr.val.length = 32 from arr.property]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show (256 : Nat) = 2 ^ 8 from by norm_num, ← Nat.pow_mul, Nat.mul_comm 8 j,
    Array.getElem!_Nat_eq]
  ring

/-! ## Splitting / reassembly lemma -/

/-- Splitting a bit list into n consecutive chunks of size k reconstructs
    the value of the first k*n bits. Heart of the from_bytes argument. -/
theorem toNat_split_chunks (bs : List Bool) (k n : Nat) (h : k * n ≤ bs.length) :
    toNat (bs.take (k * n)) =
      ∑ i ∈ Finset.range n,
        toNat (bs.extract (k * i) (k * i + k)) * 2 ^ (k * i) := by
  induction n with
  | zero => simp [toNat]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hkn : k * n ≤ bs.length := by nlinarith
    -- Split: take (k*(n+1)) = take (k*n) ++ extract (k*n) (k*n+k)
    have hsplit : bs.take (k * (n + 1)) = bs.take (k * n) ++
        bs.extract (k * n) (k * n + k) := by
      rw [show k * (n + 1) = k * n + k from by ring]
      rw [extract_eq_drop_take]
      conv_lhs => rw [← take_append_drop (k * n) (bs.take (k * n + k))]
      rw [take_take, drop_take]
      simp
    rw [hsplit, toNat_append]
    have hlen : (bs.take (k * n)).length = k * n := by
      rw [length_take]; omega
    rw [hlen, ih hkn]

/-! ## Scalar52 limb-array to bit list -/

/-- Convert a list of U64 limbs (each representing `w` bits) to a flat bit list. -/
def ofLimbList (w : Nat) (limbs : List U64) : List Bool :=
  (limbs.map (fun l => ofNat w l.val)).flatten

/-- Convert a Scalar52 (5 limbs × 52 bits) to a 260-bit list. -/
def ofScalar52 (arr : Array U64 5#usize) : List Bool :=
  ofLimbList 52 arr.val

theorem ofLimbList_length (w : Nat) (limbs : List U64) :
    (ofLimbList w limbs).length = w * limbs.length := by
  induction limbs with
  | nil => simp [ofLimbList]
  | cons x xs ih =>
    unfold ofLimbList
    simp only [map_cons, flatten_cons, length_append, ofNat_length]
    change w + (ofLimbList w xs).length = w * (xs.length + 1)
    rw [ih]; ring

theorem ofScalar52_length (arr : Array U64 5#usize) :
    (ofScalar52 arr).length = 260 := by
  simp [ofScalar52, ofLimbList_length, arr.property]

/-- The value of a Scalar52's bits equals `Scalar52_as_Nat`. -/
theorem toNat_ofScalar52 (arr : Array U64 5#usize)
    (h : ∀ i : Fin 5, arr[i]!.val < 2 ^ 52) :
    toNat (ofScalar52 arr) = Scalar52_as_Nat arr := by
  unfold ofScalar52 ofLimbList Scalar52_as_Nat
  have hlen : arr.val.length = 5 := arr.property
  -- Destructure into 5 elements
  match arr, hlen with
  | ⟨[a0, a1, a2, a3, a4], _⟩, _ =>
  simp only [map_cons, map_nil, flatten_cons, flatten_nil, append_nil]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  simp only [Array.getElem!_Nat_eq, List.getElem!_cons_zero, List.getElem!_cons_succ]
  rw [toNat_append, toNat_append, toNat_append, toNat_append]
  simp only [ofNat_length]
  have h0 : a0.val < 2 ^ 52 := by have := h ⟨0, by omega⟩; simpa [Array.getElem!_Nat_eq] using this
  have h1 : a1.val < 2 ^ 52 := by have := h ⟨1, by omega⟩; simpa [Array.getElem!_Nat_eq] using this
  have h2 : a2.val < 2 ^ 52 := by have := h ⟨2, by omega⟩; simpa [Array.getElem!_Nat_eq] using this
  have h3 : a3.val < 2 ^ 52 := by have := h ⟨3, by omega⟩; simpa [Array.getElem!_Nat_eq] using this
  have h4 : a4.val < 2 ^ 52 := by have := h ⟨4, by omega⟩; simpa [Array.getElem!_Nat_eq] using this
  rw [toNat_ofNat 52 a0.val h0, toNat_ofNat 52 a1.val h1,
    toNat_ofNat 52 a2.val h2, toNat_ofNat 52 a3.val h3,
    toNat_ofNat 52 a4.val h4]
  ring

/-- The value of a 32-byte array's bits equals `U8x32_as_Nat`. -/
theorem toNat_ofByteArray' (arr : Array U8 32#usize) :
    toNat (ofByteArray arr) = U8x32_as_Nat arr :=
  toNat_ofByteArray arr

end BitList
