/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.Basic

/-! # List Bool bit manipulation infrastructure

Definitions and lemmas for reasoning about bit-level operations using `List Bool`.
The key idea is that bitwise operations like shifts and masks correspond to simple
list operations (`List.drop`, `List.take`, `List.extract`).

## Convention

All bit lists are **LSB-first**: the head of the list is bit 0 (least significant).
-/

open Aeneas Aeneas.Std

namespace BitList

/-! ## Core definitions -/

/-- Interpret a list of booleans as a natural number (LSB-first).
    `toNat [true, false, true] = 1 + 0 + 4 = 5` -/
def toNat : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * toNat bs

/-- Convert a natural number to a fixed-width bit list (LSB-first).
    `ofNat 4 5 = [true, false, true, false]` -/
def ofNat : Nat → Nat → List Bool
  | 0, _ => []
  | w + 1, n => (n % 2 == 1) :: ofNat w (n / 2)

/-- Two bit lists are equivalent if they agree at every position, treating
    out-of-bounds positions as `false` (zero-extension).
    This captures "same numeric value, possibly different widths". -/
def Equiv (bs₁ bs₂ : List Bool) : Prop :=
  ∀ i : Nat, bs₁.getD i false = bs₂.getD i false

scoped infix:50 " ≈ₗ " => BitList.Equiv

/-! ## Scalar type conversions -/

/-- 8-bit LSB-first representation of a U8 value. -/
def ofU8 (x : U8) : List Bool := ofNat 8 x.val

/-- 64-bit LSB-first representation of a U64 value. -/
def ofU64 (x : U64) : List Bool := ofNat 64 x.val

/-- Convert a list of bytes to a flat bit list (LSB-first within each byte,
    bytes in list order). -/
def ofByteList (bytes : List U8) : List Bool :=
  bytes.bind ofU8

/-- Convert a 32-byte array to a 256-bit list. -/
def ofByteArray (arr : Array U8 32#usize) : List Bool :=
  ofByteList arr.val

/-! ## Equiv: basic properties -/

theorem Equiv.refl (bs : List Bool) : bs ≈ₗ bs :=
  fun _ => rfl

theorem Equiv.symm (h : bs₁ ≈ₗ bs₂) : bs₂ ≈ₗ bs₁ :=
  fun i => (h i).symm

theorem Equiv.trans (h₁ : bs₁ ≈ₗ bs₂) (h₂ : bs₂ ≈ₗ bs₃) : bs₁ ≈ₗ bs₃ :=
  fun i => (h₁ i).trans (h₂ i)

/-- Appending `false` bits does not change equivalence. -/
theorem Equiv.append_false (bs : List Bool) (n : Nat) :
    bs ++ List.replicate n false ≈ₗ bs := by
  sorry
  -- For i < bs.length: getD agrees (append doesn't affect).
  -- For i ≥ bs.length: both sides return false. ✓

/-- Equiv implies the same numeric value. -/
theorem Equiv.toNat_eq (h : bs₁ ≈ₗ bs₂) : toNat bs₁ = toNat bs₂ := by
  sorry
  -- Both toNat values equal ∑ i, (bs.getD i false).toNat * 2^i.
  -- Since h says getD agrees at every position, the sums are equal. ✓

/-- Equiv is preserved by `List.extract` on both sides. -/
theorem Equiv.extract (h : bs₁ ≈ₗ bs₂) (start stop : Nat) :
    bs₁.extract start stop ≈ₗ bs₂.extract start stop := by
  sorry
  -- extract takes a subrange; getD on extract at position i corresponds
  -- to getD on the original at position (start + i), which agrees by h. ✓

/-! ## Length lemmas -/

/-- `ofNat w n` always produces exactly `w` bits. -/
theorem ofNat_length (w n : Nat) : (ofNat w n).length = w := by
  sorry
  -- By induction on w.

theorem ofU8_length (x : U8) : (ofU8 x).length = 8 :=
  ofNat_length 8 x.val

theorem ofU64_length (x : U64) : (ofU64 x).length = 64 :=
  ofNat_length 64 x.val

theorem ofByteList_length (bytes : List U8) :
    (ofByteList bytes).length = 8 * bytes.length := by
  sorry
  -- By induction on bytes. Each byte contributes 8 bits.

theorem ofByteArray_length (arr : Array U8 32#usize) :
    (ofByteArray arr).length = 256 := by
  sorry
  -- 8 * 32 = 256, by ofByteList_length.

/-! ## Pure List Bool lemmas: `ofNat` interacts with list operations

These are the primary lemmas, stated as equalities between `List Bool` values. -/

/-- Taking fewer bits gives the narrower representation (mask is take). -/
theorem ofNat_take (k w : Nat) (n : Nat) (hkw : k ≤ w) :
    (ofNat w n).take k = ofNat k n := by
  sorry
  -- By induction on k, generalizing w and n.

/-- Dropping bits gives the shifted representation (shift is drop). -/
theorem ofNat_drop (k w : Nat) (n : Nat) (hkw : k ≤ w) :
    (ofNat w n).drop k = ofNat (w - k) (n / 2 ^ k) := by
  sorry
  -- By induction on k, generalizing w and n.

/-- Extracting a range of bits gives the shifted, narrower representation. -/
theorem ofNat_extract (w start len : Nat) (n : Nat)
    (h : start + len ≤ w) :
    (ofNat w n).extract start (start + len) = ofNat len (n / 2 ^ start) := by
  sorry
  -- Combines ofNat_drop and ofNat_take.

/-- Splitting a bit list gives two shorter bit lists. -/
theorem ofNat_split (w₁ w₂ : Nat) (n : Nat) :
    ofNat (w₁ + w₂) n = ofNat w₁ n ++ ofNat w₂ (n / 2 ^ w₁) := by
  sorry
  -- By induction on w₁, generalizing n.

/-- `ofNat w` ignores bits above position w: `ofNat w (n % 2^w) = ofNat w n`. -/
theorem ofNat_mod (w n : Nat) :
    ofNat w (n % 2 ^ w) = ofNat w n := by
  sorry
  -- By induction on w, generalizing n.
  -- Key identities: (n % 2^(w+1)) % 2 = n % 2, (n % 2^(w+1)) / 2 = (n/2) % 2^w.

/-- A wider representation is Equiv to a narrower one when the value fits. -/
theorem ofNat_equiv_of_lt (k w : Nat) (n : Nat) (hkw : k ≤ w) (hn : n < 2 ^ k) :
    ofNat w n ≈ₗ ofNat k n := by
  sorry
  -- ofNat w n = ofNat k n ++ ofNat (w-k) 0   [ofNat_split + n/2^k = 0]
  -- By Equiv.append_false. ✓

/-! ## Composing extracts -/

/-- Extracting from an extract composes: takes the sub-subrange. -/
theorem extract_extract (l : List α) (a b c d : Nat) (hcd : c + d ≤ b - a) :
    (l.extract a b).extract c (c + d) = l.extract (a + c) (a + c + d) := by
  sorry
  -- Uses: extract = drop then take, drop/take composition.

/-! ## Byte list decomposition into bits -/

/-- The bits of a cons byte list are the head byte's bits followed by the tail's. -/
theorem ofByteList_cons (x : U8) (xs : List U8) :
    ofByteList (x :: xs) = ofU8 x ++ ofByteList xs := by
  sorry -- Immediate from the definition of List.bind.

/-- Extracting 8-aligned bits from a byte list = extracting the corresponding bytes. -/
theorem ofByteList_extract (bytes : List U8) (i j : Nat)
    (h : j ≤ bytes.length) :
    (ofByteList bytes).extract (8 * i) (8 * j) =
      ofByteList (bytes.extract i j) := by
  sorry
  -- By induction on bytes. Each byte contributes exactly 8 bits.

/-! ## Round-trip and bridge lemmas (connecting to Nat) -/

/-- Converting to bits and back recovers the original value. -/
theorem toNat_ofNat (w n : Nat) (h : n < 2 ^ w) : toNat (ofNat w n) = n := by
  sorry
  -- By induction on w. Uses Nat.mod_add_div.

theorem toNat_ofU8 (x : U8) : toNat (ofU8 x) = x.val := by
  sorry -- toNat_ofNat + x.val < 2^8.

theorem toNat_ofU64 (x : U64) : toNat (ofU64 x) = x.val := by
  sorry -- toNat_ofNat + x.val < 2^64.

/-- If a bit list has length w, converting to Nat and back gives the same list. -/
theorem ofNat_toNat (bs : List Bool) :
    ofNat bs.length (toNat bs) = bs := by
  sorry
  -- By induction on bs.

/-- A bit list's value is bounded by `2^length`. -/
theorem toNat_lt_pow (bs : List Bool) : toNat bs < 2 ^ bs.length := by
  sorry
  -- By induction on bs.

/-- Appending two bit lists adds their values with the appropriate shift. -/
theorem toNat_append (bs₁ bs₂ : List Bool) :
    toNat (bs₁ ++ bs₂) = toNat bs₁ + toNat bs₂ * 2 ^ bs₁.length := by
  sorry
  -- By induction on bs₁.

/-- Taking k bits gives the value mod 2^k. -/
theorem toNat_take (k : Nat) (bs : List Bool) :
    toNat (bs.take k) = toNat bs % 2 ^ k := by
  sorry

/-- Dropping k bits gives the value divided by 2^k. -/
theorem toNat_drop (k : Nat) (bs : List Bool) :
    toNat (bs.drop k) = toNat bs / 2 ^ k := by
  sorry

/-- The value of a byte list's bits equals the base-256 interpretation. -/
theorem toNat_ofByteList (bytes : List U8) :
    toNat (ofByteList bytes) = Nat.ofDigits 256 (bytes.map (·.val)) := by
  sorry
  -- By induction on bytes using toNat_append and toNat_ofU8.

/-- The value of a 32-byte array's bits equals U8x32_as_Nat. -/
theorem toNat_ofByteArray (arr : Array U8 32#usize) :
    toNat (ofByteArray arr) = U8x32_as_Nat arr := by
  sorry
  -- From toNat_ofByteList and U8x32_as_Nat_is_NatofDigits.

/-! ## Splitting / reassembly lemma -/

/-- Splitting a bit list into n consecutive chunks of size k reconstructs
    the value of the first k*n bits. Heart of the from_bytes argument. -/
theorem toNat_split_chunks (bs : List Bool) (k n : Nat) (h : k * n ≤ bs.length) :
    toNat (bs.take (k * n)) =
      ∑ i ∈ Finset.range n,
        toNat (bs.extract (k * i) (k * i + k)) * 2 ^ (k * i) := by
  sorry
  -- By induction on n. Uses toNat_append.

end BitList
