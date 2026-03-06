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
  -- For i < bs.length: (bs ++ replicate n false).getD i false = bs.getD i false
  --   (the appended part doesn't affect positions within bs).
  -- For bs.length ≤ i < bs.length + n: getD gives false (from replicate), matching
  --   bs.getD i false = false (out of bounds).
  -- For i ≥ bs.length + n: both return false (out of bounds). ✓

/-- Equiv implies the same numeric value. -/
theorem Equiv.toNat_eq (h : bs₁ ≈ₗ bs₂) : toNat bs₁ = toNat bs₂ := by
  sorry
  -- Both toNat values equal ∑ i, (bs.getD i false).toNat * 2^i.
  -- Since h says getD agrees at every position, the sums are equal. ✓

/-- A bit list is equivalent to its take-k if the remaining bits are all false. -/
theorem Equiv.of_take (bs : List Bool) (k : Nat)
    (h : ∀ i, k ≤ i → bs.getD i false = false) :
    bs ≈ₗ bs.take k := by
  sorry
  -- For i < k: bs.getD i false = (bs.take k).getD i false (take preserves within range).
  -- For i ≥ k: bs.getD i false = false (by h), and (bs.take k).getD i false = false
  --   (out of bounds since (bs.take k).length ≤ k). ✓

/-! ## Length lemmas -/

/-- `ofNat w n` always produces exactly `w` bits. -/
theorem ofNat_length (w n : Nat) : (ofNat w n).length = w := by
  sorry
  -- By induction on w.
  -- Base: ofNat 0 n = [], length 0.
  -- Step: ofNat (w+1) n = _ :: ofNat w (n/2), length = 1 + w = w + 1.

theorem ofU8_length (x : U8) : (ofU8 x).length = 8 :=
  ofNat_length 8 x.val

theorem ofU64_length (x : U64) : (ofU64 x).length = 64 :=
  ofNat_length 64 x.val

theorem ofByteList_length (bytes : List U8) :
    (ofByteList bytes).length = 8 * bytes.length := by
  sorry
  -- By induction on bytes.
  -- Base: [].bind ofU8 = [], length 0 = 8 * 0.
  -- Step: (x :: xs).bind ofU8 = ofU8 x ++ xs.bind ofU8,
  --   length = 8 + 8 * xs.length = 8 * (xs.length + 1).

theorem ofByteArray_length (arr : Array U8 32#usize) :
    (ofByteArray arr).length = 256 := by
  sorry
  -- ofByteArray arr = ofByteList arr.val, arr.val.length = 32,
  -- so length = 8 * 32 = 256, by ofByteList_length.

/-! ## Pure List Bool lemmas: `ofNat` interacts with list operations

These are the primary lemmas. They express how `take`, `drop`, and `extract`
on bit lists correspond to arithmetic operations — but stated as equalities
between `List Bool` values, not between `Nat` values. -/

/-- Taking fewer bits from a bit representation gives the narrower representation.
    This is the List Bool version of "masking to k bits". -/
theorem ofNat_take (k w : Nat) (n : Nat) (hkw : k ≤ w) :
    (ofNat w n).take k = ofNat k n := by
  sorry
  -- By induction on k, generalizing w and n.
  -- Base: take 0 of anything = [] = ofNat 0 n. ✓
  -- Step: w = w' + 1 (since k+1 ≤ w), so ofNat w n = (n%2==1) :: ofNat w' (n/2).
  --   take (k+1) = (n%2==1) :: take k (ofNat w' (n/2))
  --              = (n%2==1) :: ofNat k (n/2)               [by IH]
  --              = ofNat (k+1) n. ✓

/-- Dropping bits from the front gives the shifted representation.
    This is the List Bool version of "right shift by k". -/
theorem ofNat_drop (k w : Nat) (n : Nat) (hkw : k ≤ w) :
    (ofNat w n).drop k = ofNat (w - k) (n / 2 ^ k) := by
  sorry
  -- By induction on k, generalizing w and n.
  -- Base: drop 0 = id, n / 2^0 = n, w - 0 = w. ✓
  -- Step: w = w' + 1 (since k+1 ≤ w), so ofNat w n = (n%2==1) :: ofNat w' (n/2).
  --   drop (k+1) = drop k (ofNat w' (n/2))
  --              = ofNat (w' - k) ((n/2) / 2^k)            [by IH]
  --              = ofNat (w - (k+1)) (n / 2^(k+1)). ✓
  --   (using (n/2)/2^k = n/2^(k+1) and w' - k = (w'+1) - (k+1))

/-- Extracting a range of bits gives the shifted, narrower representation.
    `(ofNat w n).extract start stop` gives bits [start, stop) of n. -/
theorem ofNat_extract (w start len : Nat) (n : Nat)
    (h : start + len ≤ w) :
    (ofNat w n).extract start (start + len) = ofNat len (n / 2 ^ start) := by
  sorry
  -- List.extract l s e = (l.drop s).take (e - s).
  -- (ofNat w n).extract start (start+len) = ((ofNat w n).drop start).take len
  --   = (ofNat (w - start) (n / 2^start)).take len          [by ofNat_drop]
  --   = ofNat len (n / 2^start)                              [by ofNat_take, since len ≤ w - start]

/-- Splitting a bit list at position k gives two shorter bit lists. -/
theorem ofNat_split (w₁ w₂ : Nat) (n : Nat) :
    ofNat (w₁ + w₂) n = ofNat w₁ n ++ ofNat w₂ (n / 2 ^ w₁) := by
  sorry
  -- By induction on w₁, generalizing n.
  -- Base: ofNat (0 + w₂) n = ofNat w₂ n, and
  --   ofNat 0 n ++ ofNat w₂ (n / 2^0) = [] ++ ofNat w₂ n = ofNat w₂ n. ✓
  -- Step: ofNat ((w₁+1) + w₂) n = (n%2==1) :: ofNat (w₁ + w₂) (n/2)
  --   = (n%2==1) :: (ofNat w₁ (n/2) ++ ofNat w₂ ((n/2) / 2^w₁))  [by IH]
  --   = ((n%2==1) :: ofNat w₁ (n/2)) ++ ofNat w₂ (n / 2^(w₁+1))
  --   = ofNat (w₁+1) n ++ ofNat w₂ (n / 2^(w₁+1)). ✓

/-- A wider representation is Equiv to a narrower one (the extra bits are zero
    when n < 2^k). -/
theorem ofNat_equiv_of_lt (k w : Nat) (n : Nat) (hkw : k ≤ w) (hn : n < 2 ^ k) :
    ofNat w n ≈ₗ ofNat k n := by
  sorry
  -- ofNat w n = ofNat k n ++ ofNat (w-k) (n / 2^k)   [by ofNat_split]
  -- Since n < 2^k, we have n / 2^k = 0, so ofNat (w-k) 0 = replicate (w-k) false.
  -- Therefore ofNat w n = ofNat k n ++ replicate (w-k) false ≈ₗ ofNat k n
  --   [by Equiv.append_false]. ✓

/-! ## Byte list decomposition into bits

These lemmas express how the bit representation of a byte list relates to
the bit representations of individual bytes and sublists. -/

/-- The bits of a cons byte list are the bits of the head byte
    followed by the bits of the tail. -/
theorem ofByteList_cons (x : U8) (xs : List U8) :
    ofByteList (x :: xs) = ofU8 x ++ ofByteList xs := by
  sorry -- Immediate from the definition of List.bind.

/-- Extracting 8-aligned bits from a byte list corresponds to
    extracting the corresponding sub-list of bytes. -/
theorem ofByteList_extract (bytes : List U8) (i j : Nat)
    (h : j ≤ bytes.length) :
    (ofByteList bytes).extract (8 * i) (8 * j) =
      ofByteList (bytes.extract i j) := by
  sorry
  -- By induction on bytes and i.
  -- The key idea: ofByteList is a flat-map of ofU8 (each producing 8 bits),
  -- so extracting at 8-aligned boundaries corresponds to extracting
  -- the underlying bytes. Each byte contributes exactly 8 bits, so
  -- bits [8i, 8j) come from bytes [i, j).

/-! ## Round-trip and bridge lemmas (connecting to Nat) -/

/-- Converting to bits and back recovers the original value. -/
theorem toNat_ofNat (w n : Nat) (h : n < 2 ^ w) : toNat (ofNat w n) = n := by
  sorry
  -- By induction on w, generalizing n.
  -- Base: n < 1, so n = 0. toNat [] = 0. ✓
  -- Step: toNat ((n%2==1) :: ofNat w (n/2))
  --   = (n%2==1).toNat + 2 * toNat (ofNat w (n/2))
  --   = (n%2) + 2 * (n/2)     [by IH, since n/2 < 2^w]
  --   = n                       [Nat.mod_add_div]

theorem toNat_ofU8 (x : U8) : toNat (ofU8 x) = x.val := by
  sorry -- Follows from toNat_ofNat since x.val < 2^8.

theorem toNat_ofU64 (x : U64) : toNat (ofU64 x) = x.val := by
  sorry -- Follows from toNat_ofNat since x.val < 2^64.

/-- A bit list's value is bounded by `2^length`. -/
theorem toNat_lt_pow (bs : List Bool) : toNat bs < 2 ^ bs.length := by
  sorry
  -- By induction on bs.
  -- Base: toNat [] = 0 < 1 = 2^0. ✓
  -- Step: toNat (b :: bs) = b.toNat + 2 * toNat bs
  --   ≤ 1 + 2 * (2^bs.length - 1) = 2^(bs.length+1) - 1 < 2^(bs.length+1). ✓

/-- Appending two bit lists adds their values with the appropriate shift. -/
theorem toNat_append (bs₁ bs₂ : List Bool) :
    toNat (bs₁ ++ bs₂) = toNat bs₁ + toNat bs₂ * 2 ^ bs₁.length := by
  sorry
  -- By induction on bs₁.
  -- Base: [] ++ bs₂ = bs₂, toNat bs₂ = 0 + toNat bs₂ * 1. ✓
  -- Step: (b :: bs₁) ++ bs₂ = b :: (bs₁ ++ bs₂).
  --   toNat = b.toNat + 2 * (toNat bs₁ + toNat bs₂ * 2^bs₁.length)   [by IH]
  --         = toNat (b :: bs₁) + toNat bs₂ * 2^(b :: bs₁).length. ✓

/-- Taking k bits gives the value mod 2^k. -/
theorem toNat_take (k : Nat) (bs : List Bool) :
    toNat (bs.take k) = toNat bs % 2 ^ k := by
  sorry
  -- Follows from toNat_append applied to bs = bs.take k ++ bs.drop k,
  -- plus the fact that toNat (bs.take k) < 2^k (by toNat_lt_pow + length of take).

/-- Dropping k bits gives the value divided by 2^k. -/
theorem toNat_drop (k : Nat) (bs : List Bool) :
    toNat (bs.drop k) = toNat bs / 2 ^ k := by
  sorry
  -- Follows from toNat_append applied to bs = bs.take k ++ bs.drop k,
  -- which gives the Euclidean division.

/-- The value of a byte list's bits equals the little-endian byte interpretation. -/
theorem toNat_ofByteList (bytes : List U8) :
    toNat (ofByteList bytes) = Nat.ofDigits 256 (bytes.map (·.val)) := by
  sorry
  -- By induction on bytes using toNat_append and toNat_ofU8.

/-- The value of a 32-byte array's bits equals U8x32_as_Nat. -/
theorem toNat_ofByteArray (arr : Array U8 32#usize) :
    toNat (ofByteArray arr) = U8x32_as_Nat arr := by
  sorry
  -- Follows from toNat_ofByteList and U8x32_as_Nat_is_NatofDigits.

/-! ## Splitting / reassembly lemma -/

/-- Splitting a bit list into n consecutive chunks of size k and weighting
    by powers of 2^k reconstructs the value of the first k*n bits.
    This is the heart of the from_bytes correctness argument. -/
theorem toNat_split_chunks (bs : List Bool) (k n : Nat) (h : k * n ≤ bs.length) :
    toNat (bs.take (k * n)) =
      ∑ i ∈ Finset.range n,
        toNat (bs.extract (k * i) (k * i + k)) * 2 ^ (k * i) := by
  sorry
  -- By induction on n.
  -- Base (n=0): take 0 = [], sum over empty range = 0. ✓
  -- Step (n → n+1): bs.take (k*(n+1)) = bs.take (k*n) ++ bs.extract (k*n) (k*n+k)
  --   By toNat_append and IH, the sum extends to range (n+1). ✓

/-! ## The pure List Bool specification for from_bytes

Each of the 5 result limbs, viewed as a 64-bit list, is `Equiv` to the
corresponding 51-bit slice of the input byte array's bit representation.

Using `Equiv` (≈ₗ) captures both facts simultaneously:
- The first 51 bits of the limb match the slice (positions 0..50 agree).
- The remaining 13 bits of the U64 are zero (positions 51..63 are `false`,
  matching the out-of-bounds `false` default of the 51-element slice).

No `.take`, no explicit padding, no lost information. -/

/-- The pure List Bool spec for from_bytes: each limb is Equiv to the
    corresponding 51-bit slice of the input's 256 bits. -/
theorem from_bytes_bitList_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      let allBits := ofByteArray bytes
      ∀ i : Fin 5,
        ofU64 result[i]! ≈ₗ allBits.extract (51 * i.val) (51 * i.val + 51) ⦄ := by
  sorry
  -- Unfold from_bytes. Each limb is computed as:
  --   (load8_at(bytes, j) >> k) & low_51_bit_mask
  --
  -- In List Bool terms, for each limb i with byte offset j and shift k:
  --   ofU64 result[i]  (64 bits)
  --   = ofNat 64 ((load8_at_val >>> k) &&& (2^51 - 1))
  --   = ofNat 64 ((load8_at_val / 2^k) % 2^51)
  --
  -- Since (load8_at_val / 2^k) % 2^51 < 2^51 < 2^64:
  --   ofNat 64 ((load8_at_val / 2^k) % 2^51)
  --     ≈ₗ ofNat 51 ((load8_at_val / 2^k) % 2^51)    [ofNat_equiv_of_lt]
  --     = ofNat 51 (load8_at_val / 2^k)                [ofNat_take applied backwards]
  --
  -- Now load8_at_val is the little-endian value of bytes[j..j+8], so its bits
  -- are allBits[8j..8j+64). Extracting bits [k, k+51):
  --   ofNat 51 (load8_at_val / 2^k)
  --   = (ofNat 64 load8_at_val).extract k (k + 51)     [ofNat_extract]
  --   = allBits.extract (8*j) (8*j+64) |>.extract k (k+51)
  --   = allBits.extract (8*j + k) (8*j + k + 51)       [extract of extract]
  --
  -- Checking each limb (8*j + k = 51*i):
  --   i=0: j=0,  k=0  → 8*0  + 0  = 0   = 51*0  ✓
  --   i=1: j=6,  k=3  → 8*6  + 3  = 51  = 51*1  ✓
  --   i=2: j=12, k=6  → 8*12 + 6  = 102 = 51*2  ✓
  --   i=3: j=19, k=1  → 8*19 + 1  = 153 = 51*3  ✓
  --   i=4: j=24, k=12 → 8*24 + 12 = 204 = 51*4  ✓

/-! ## Bridge: List Bool spec implies Nat spec -/

/-- Equiv implies the limb value equals the slice value. Combined with
    toNat_split_chunks, this bridges to the full Nat spec. -/
theorem field51_eq_of_bitList
    (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ
        (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    Field51_as_Nat result = U8x32_as_Nat bytes % 2 ^ 255 := by
  sorry
  -- For each i:
  --   result[i].val = toNat (ofU64 result[i])                  [toNat_ofU64]
  --                 = toNat (allBits.extract (51*i) (51*i+51)) [Equiv.toNat_eq from hequiv]
  --
  -- Therefore:
  --   Field51_as_Nat = ∑ i, result[i].val * 2^(51*i)
  --     = ∑ i, toNat (allBits.extract (51*i) (51*i+51)) * 2^(51*i)
  --     = toNat (allBits.take 255)                [toNat_split_chunks, k=51, n=5]
  --     = toNat (ofByteArray bytes) % 2^255       [toNat_take]
  --     = U8x32_as_Nat bytes % 2^255              [toNat_ofByteArray]

/-- The limb bound result[i] < 2^51 also follows from Equiv. -/
theorem limb_bound_of_equiv
    (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ
        (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    ∀ i : Fin 5, result[i]!.val < 2 ^ 51 := by
  sorry
  -- For each i:
  --   result[i].val = toNat (ofU64 result[i])                  [toNat_ofU64]
  --                 = toNat (allBits.extract (51*i) (51*i+51)) [Equiv.toNat_eq]
  -- The extract has length ≤ 51, so by toNat_lt_pow:
  --   toNat (allBits.extract (51*i) (51*i+51)) < 2^(extract.length) ≤ 2^51. ✓

end BitList
