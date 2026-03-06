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
  -- Step: take (k+1) (ofNat (w'+1) n) = (n%2==1) :: take k (ofNat w' (n/2))
  --   = (n%2==1) :: ofNat k (n/2) = ofNat (k+1) n. ✓

/-- Dropping bits gives the shifted representation (shift is drop). -/
theorem ofNat_drop (k w : Nat) (n : Nat) (hkw : k ≤ w) :
    (ofNat w n).drop k = ofNat (w - k) (n / 2 ^ k) := by
  sorry
  -- By induction on k, generalizing w and n.
  -- Step: drop (k+1) = drop k (ofNat w' (n/2)) = ofNat (w-(k+1)) (n/2^(k+1)). ✓

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
  -- Base: both sides are []. ✓
  -- Step: ofNat (w+1) (n % 2^(w+1))
  --   = ((n % 2^(w+1)) % 2 == 1) :: ofNat w ((n % 2^(w+1)) / 2)
  --   The key identities:
  --     (n % 2^(w+1)) % 2 = n % 2
  --       [since 2 | 2^(w+1), we have n % 2^(w+1) % 2 = n % 2]
  --     (n % 2^(w+1)) / 2 = (n / 2) % 2^w
  --       [standard: (n % (2*m)) / 2 = (n/2) % m]
  --   So = (n%2==1) :: ofNat w ((n/2) % 2^w)
  --      = (n%2==1) :: ofNat w (n/2)           [by IH]
  --      = ofNat (w+1) n. ✓

/-- A wider representation is Equiv to a narrower one when the value fits. -/
theorem ofNat_equiv_of_lt (k w : Nat) (n : Nat) (hkw : k ≤ w) (hn : n < 2 ^ k) :
    ofNat w n ≈ₗ ofNat k n := by
  sorry
  -- ofNat w n = ofNat k n ++ ofNat (w-k) (n / 2^k)   [ofNat_split]
  -- Since n < 2^k, n / 2^k = 0, so the tail is all false.
  -- By Equiv.append_false. ✓

/-! ## Composing extracts -/

/-- Extracting from an extract composes: takes the sub-subrange. -/
theorem extract_extract (l : List α) (a b c d : Nat) (hcd : c + d ≤ b - a) :
    (l.extract a b).extract c (c + d) = l.extract (a + c) (a + c + d) := by
  sorry
  -- extract l a b = (l.drop a).take (b - a).
  -- Applying extract c (c+d) to that:
  --   ((l.drop a).take (b-a)).drop c |>.take d
  --   = (l.drop a).drop c |>.take d          [drop of take when c ≤ b-a]
  --   = (l.drop (a+c)).take d
  --   = l.extract (a+c) (a+c+d). ✓

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
  -- By induction on bytes. Each byte contributes exactly 8 bits,
  -- so 8-aligned bit extraction maps to byte extraction.

/-! ## Round-trip and bridge lemmas (connecting to Nat) -/

/-- Converting to bits and back recovers the original value. -/
theorem toNat_ofNat (w n : Nat) (h : n < 2 ^ w) : toNat (ofNat w n) = n := by
  sorry
  -- By induction on w. Uses Nat.mod_add_div.

theorem toNat_ofU8 (x : U8) : toNat (ofU8 x) = x.val := by
  sorry -- toNat_ofNat + x.val < 2^8.

theorem toNat_ofU64 (x : U64) : toNat (ofU64 x) = x.val := by
  sorry -- toNat_ofNat + x.val < 2^64.

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
  -- From toNat_append on bs = bs.take k ++ bs.drop k.

/-- Dropping k bits gives the value divided by 2^k. -/
theorem toNat_drop (k : Nat) (bs : List Bool) :
    toNat (bs.drop k) = toNat bs / 2 ^ k := by
  sorry
  -- From toNat_append on bs = bs.take k ++ bs.drop k.

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

/-! ## The pure List Bool specification for from_bytes

Each of the 5 result limbs is `Equiv` to the corresponding 51-bit slice.
`Equiv` captures both the bit-match and the zero-padding simultaneously. -/

/-- The pure List Bool spec for from_bytes. -/
theorem from_bytes_bitList_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      let allBits := ofByteArray bytes
      ∀ i : Fin 5,
        ofU64 result[i]! ≈ₗ allBits.extract (51 * i.val) (51 * i.val + 51) ⦄ := by
  sorry
  -- **Proof sketch**: Unfold from_bytes. For each limb i with byte offset j
  -- and shift k, the computation is:
  --   result[i] = (load8_at(bytes.to_slice, j) >>> k) &&& low_51_bit_mask
  --
  -- Step 1 (load8_at): By load8_at_bitList_spec,
  --   ofU64 (load8_at s j) = (ofByteList s.val).extract (8*j) (8*j + 64)
  --   Since s = bytes.to_slice, s.val = bytes.val, so
  --   = (ofByteArray bytes).extract (8*j) (8*j + 64)
  --
  -- Step 2 (shift + mask): The value after >>> k and &&& mask is
  --   ((load8_at_val.val / 2^k) % 2^51)
  --   Using Aeneas specs: U64.ShiftRight_spec gives z.val = x.val >>> y.val,
  --   UScalar.val_and gives (x &&& y).val = x.val &&& y.val,
  --   Nat.shiftRight_eq gives >>> = / 2^k,
  --   land_pow_two_sub_one_eq_mod gives &&& (2^51-1) = % 2^51.
  --
  -- Step 3 (convert to List Bool):
  --   ofU64 result[i] = ofNat 64 ((load8_at_val / 2^k) % 2^51)
  --   ≈ₗ ofNat 51 ((load8_at_val / 2^k) % 2^51)   [ofNat_equiv_of_lt]
  --   = ofNat 51 (load8_at_val / 2^k)               [ofNat_mod]
  --   = (ofNat 64 load8_at_val).extract k (k+51)    [ofNat_extract]
  --   = allBits.extract (8*j) (8*j+64) |>.extract k (k+51)  [load8_at result]
  --   = allBits.extract (8*j+k) (8*j+k+51)          [extract_extract]
  --
  -- Step 4 (check 8*j + k = 51*i for each limb):
  --   i=0: j=0,  k=0  → 0   = 51*0  ✓
  --   i=1: j=6,  k=3  → 51  = 51*1  ✓
  --   i=2: j=12, k=6  → 102 = 51*2  ✓
  --   i=3: j=19, k=1  → 153 = 51*3  ✓
  --   i=4: j=24, k=12 → 204 = 51*4  ✓

/-! ## load8_at specification

`load8_at` loads 8 consecutive bytes from a slice and packs them into a U64
in little-endian order. In List Bool terms, the result's bits are exactly
the 64 bits starting at position `8*i` in the slice's bit representation. -/

/-- The Nat-level spec for load8_at: the result is the little-endian
    combination of 8 consecutive bytes. -/
theorem load8_at_val_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      result.val = ∑ j ∈ Finset.range 8,
        input[i.val + j]!.val * 2 ^ (8 * j) ⦄ := by
  sorry
  -- Unfold load8_at. It computes:
  --   input[i] | (input[i+1] << 8) | ... | (input[i+7] << 56)
  --
  -- At the Nat level, OR on disjoint bit ranges equals addition:
  --   (a ||| (b <<< 8k)).val = a.val + b.val * 2^(8k)
  -- when a.val < 2^(8k) (no overlap).
  --
  -- By Aeneas specs:
  --   UScalar.cast_val: cast to U64 preserves the value (U8 < 2^64)
  --   U64.ShiftLeft_spec: (x <<< k).val = x.val * 2^k (when no overflow)
  --   UScalar.val_or: (x ||| y).val = x.val ||| y.val
  --
  -- The disjoint-OR-equals-addition argument:
  --   Each byte b[j] is cast to U64 and shifted left by 8*j bits.
  --   The shifted values occupy disjoint 8-bit ranges [8j, 8j+8).
  --   OR on disjoint ranges = addition.
  --
  -- This gives result.val = ∑ j, input[i+j].val * 2^(8*j). ✓

/-- The List Bool spec for load8_at: the result's bits are exactly
    the 64 bits starting at byte position i in the input. -/
theorem load8_at_bitList_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      ofU64 result = (ofByteList input.val).extract (8 * i.val) (8 * i.val + 64) ⦄ := by
  sorry
  -- From load8_at_val_spec:
  --   result.val = ∑ j, input[i+j].val * 2^(8*j)
  --             = toNat (ofByteList (input.val.extract i.val (i.val + 8)))
  --                     [by toNat_ofByteList on the 8-byte sublist]
  --
  -- So ofU64 result = ofNat 64 result.val
  --   = ofNat 64 (toNat (ofByteList (input.val.extract i.val (i.val+8))))
  --
  -- The byte sublist has 8 bytes → 64 bits, and its toNat < 2^64.
  -- By toNat_ofNat round-trip:
  --   ofNat 64 (toNat bs) = bs    when bs.length = 64
  --
  -- So ofU64 result = ofByteList (input.val.extract i.val (i.val + 8))
  --   = (ofByteList input.val).extract (8*i.val) (8*i.val + 64)  [ofByteList_extract]

/-! ## Additional lemma: ofNat round-trip for bit lists -/

/-- If a bit list has length w, converting to Nat and back gives the same list. -/
theorem ofNat_toNat (bs : List Bool) :
    ofNat bs.length (toNat bs) = bs := by
  sorry
  -- By induction on bs.
  -- Base: ofNat 0 0 = []. ✓
  -- Step: ofNat (bs.length+1) (b.toNat + 2 * toNat bs)
  --   = ((b.toNat + 2 * toNat bs) % 2 == 1) :: ofNat bs.length ((b.toNat + 2 * toNat bs) / 2)
  --   = (b.toNat % 2 == 1) :: ofNat bs.length (toNat bs)   [div/mod of b.toNat + 2*k]
  --   = b :: bs                                              [by IH + b.toNat % 2 determines b]

/-! ## Bridge: List Bool spec implies Nat spec -/

/-- Equiv implies the limb value equals the slice value. -/
theorem field51_eq_of_bitList
    (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ
        (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    Field51_as_Nat result = U8x32_as_Nat bytes % 2 ^ 255 := by
  sorry
  -- For each i:
  --   result[i].val = toNat (ofU64 result[i])                  [toNat_ofU64]
  --                 = toNat (allBits.extract (51*i) (51*i+51)) [Equiv.toNat_eq]
  -- Field51_as_Nat = ∑ i, result[i].val * 2^(51*i)
  --   = ∑ i, toNat (allBits.extract (51*i) (51*i+51)) * 2^(51*i)
  --   = toNat (allBits.take 255)                [toNat_split_chunks, k=51, n=5]
  --   = toNat (ofByteArray bytes) % 2^255       [toNat_take]
  --   = U8x32_as_Nat bytes % 2^255              [toNat_ofByteArray]

/-- The limb bound follows from Equiv (the extract has length ≤ 51). -/
theorem limb_bound_of_equiv
    (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ
        (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    ∀ i : Fin 5, result[i]!.val < 2 ^ 51 := by
  sorry
  -- result[i].val = toNat (ofU64 result[i])    [toNat_ofU64]
  --              = toNat (extract ...)           [Equiv.toNat_eq]
  -- extract has length ≤ 51, so toNat < 2^51   [toNat_lt_pow]. ✓

end BitList
