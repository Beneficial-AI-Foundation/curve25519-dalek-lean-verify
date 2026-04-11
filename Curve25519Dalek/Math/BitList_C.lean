/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Curve25519Dalek.Math.Basic

/-! # Nat-level bridge lemma for `Scalar52::to_bytes`

A single bridge lemma proving that 32 bytes constructed from 5 limbs via shift/mask/OR
reconstruct the same Nat value.
-/

set_option linter.style.whitespace false

open Aeneas Aeneas.Std

/-! ## Per-limb reconstruction sub-lemmas

These establish that extracting bytes from a limb and reassembling recovers the limb value.
Each is proved by `omega` on a single bounded variable (the limb value). -/

/-- For limb 0 (or 2): 6 full bytes + overflow nibble reconstruct the limb. -/
private theorem limb_full_recon (l : Nat) (hl : l < 2 ^ 52) :
    l % 256 +
    l / 2 ^ 8 % 256 * 2 ^ 8 +
    l / 2 ^ 16 % 256 * 2 ^ 16 +
    l / 2 ^ 24 % 256 * 2 ^ 24 +
    l / 2 ^ 32 % 256 * 2 ^ 32 +
    l / 2 ^ 40 % 256 * 2 ^ 40 +
    l / 2 ^ 48 * 2 ^ 48 = l := by omega

/-- For limb 1 (or 3): nibble + 6 shifted bytes reconstruct the limb. -/
private theorem limb_shifted_recon (l : Nat) (hl : l < 2 ^ 52) :
    l % 2 ^ 4 +
    l / 2 ^ 4 % 256 * 2 ^ 4 +
    l / 2 ^ 12 % 256 * 2 ^ 12 +
    l / 2 ^ 20 % 256 * 2 ^ 20 +
    l / 2 ^ 28 % 256 * 2 ^ 28 +
    l / 2 ^ 36 % 256 * 2 ^ 36 +
    l / 2 ^ 44 % 256 * 2 ^ 44 = l := by omega

/-- For limb 4 (48-bit): 6 full bytes reconstruct the limb. -/
private theorem limb4_recon (l : Nat) (hl : l < 2 ^ 48) :
    l % 256 +
    l / 2 ^ 8 % 256 * 2 ^ 8 +
    l / 2 ^ 16 % 256 * 2 ^ 16 +
    l / 2 ^ 24 % 256 * 2 ^ 24 +
    l / 2 ^ 32 % 256 * 2 ^ 32 +
    l / 2 ^ 40 % 256 * 2 ^ 40 = l := by omega

/-! ## Shared byte decomposition -/

/-- At a shared byte: `(l0 / 2^48 + l1 * 16) % 256` splits into non-overlapping nibbles. -/
private theorem shared_byte_split (l0 l1 : Nat) (hl0 : l0 < 2 ^ 52) :
    (l0 / 2 ^ 48 + l1 * 2 ^ 4) % 256 =
    l0 / 2 ^ 48 + l1 % 2 ^ 4 * 2 ^ 4 := by omega

/-! ## The main bridge lemma -/

/-- **Bridge lemma**: Given 5 limbs (each < 2^52, last < 2^48) and 32 bytes defined by the
standard shift/mask/OR pattern, the base-256 byte sum equals the base-2^52 limb sum.

The proof substitutes byte definitions, splits the shared bytes, applies per-limb reconstruction
lemmas, and closes with `omega`. -/
theorem to_bytes_bridge
    (l0 l1 l2 l3 l4 : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Nat)
    (b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Nat)
    (hl0 : l0 < 2 ^ 52) (hl1 : l1 < 2 ^ 52) (hl2 : l2 < 2 ^ 52) (hl3 : l3 < 2 ^ 52)
    (hl4 : l4 < 2 ^ 48)
    (hb0  : b0  = l0 % 256)
    (hb1  : b1  = l0 / 2 ^ 8 % 256)
    (hb2  : b2  = l0 / 2 ^ 16 % 256)
    (hb3  : b3  = l0 / 2 ^ 24 % 256)
    (hb4  : b4  = l0 / 2 ^ 32 % 256)
    (hb5  : b5  = l0 / 2 ^ 40 % 256)
    (hb6  : b6  = (l0 / 2 ^ 48 + l1 * 2 ^ 4) % 256)
    (hb7  : b7  = l1 / 2 ^ 4 % 256)
    (hb8  : b8  = l1 / 2 ^ 12 % 256)
    (hb9  : b9  = l1 / 2 ^ 20 % 256)
    (hb10 : b10 = l1 / 2 ^ 28 % 256)
    (hb11 : b11 = l1 / 2 ^ 36 % 256)
    (hb12 : b12 = l1 / 2 ^ 44 % 256)
    (hb13 : b13 = l2 % 256)
    (hb14 : b14 = l2 / 2 ^ 8 % 256)
    (hb15 : b15 = l2 / 2 ^ 16 % 256)
    (hb16 : b16 = l2 / 2 ^ 24 % 256)
    (hb17 : b17 = l2 / 2 ^ 32 % 256)
    (hb18 : b18 = l2 / 2 ^ 40 % 256)
    (hb19 : b19 = (l2 / 2 ^ 48 + l3 * 2 ^ 4) % 256)
    (hb20 : b20 = l3 / 2 ^ 4 % 256)
    (hb21 : b21 = l3 / 2 ^ 12 % 256)
    (hb22 : b22 = l3 / 2 ^ 20 % 256)
    (hb23 : b23 = l3 / 2 ^ 28 % 256)
    (hb24 : b24 = l3 / 2 ^ 36 % 256)
    (hb25 : b25 = l3 / 2 ^ 44 % 256)
    (hb26 : b26 = l4 % 256)
    (hb27 : b27 = l4 / 2 ^ 8 % 256)
    (hb28 : b28 = l4 / 2 ^ 16 % 256)
    (hb29 : b29 = l4 / 2 ^ 24 % 256)
    (hb30 : b30 = l4 / 2 ^ 32 % 256)
    (hb31 : b31 = l4 / 2 ^ 40 % 256) :
    b0 + b1 * 2 ^ 8 + b2 * 2 ^ 16 + b3 * 2 ^ 24 + b4 * 2 ^ 32 + b5 * 2 ^ 40 +
    b6 * 2 ^ 48 + b7 * 2 ^ 56 + b8 * 2 ^ 64 + b9 * 2 ^ 72 + b10 * 2 ^ 80 +
    b11 * 2 ^ 88 + b12 * 2 ^ 96 + b13 * 2 ^ 104 + b14 * 2 ^ 112 + b15 * 2 ^ 120 +
    b16 * 2 ^ 128 + b17 * 2 ^ 136 + b18 * 2 ^ 144 + b19 * 2 ^ 152 +
    b20 * 2 ^ 160 + b21 * 2 ^ 168 + b22 * 2 ^ 176 + b23 * 2 ^ 184 +
    b24 * 2 ^ 192 + b25 * 2 ^ 200 + b26 * 2 ^ 208 + b27 * 2 ^ 216 +
    b28 * 2 ^ 224 + b29 * 2 ^ 232 + b30 * 2 ^ 240 + b31 * 2 ^ 248 =
    l0 + l1 * 2 ^ 52 + l2 * 2 ^ 104 + l3 * 2 ^ 156 + l4 * 2 ^ 208 := by
  -- Substitute all byte definitions
  subst hb0; subst hb1; subst hb2; subst hb3; subst hb4; subst hb5
  subst hb7; subst hb8; subst hb9; subst hb10; subst hb11; subst hb12
  subst hb13; subst hb14; subst hb15; subst hb16; subst hb17; subst hb18
  subst hb20; subst hb21; subst hb22; subst hb23; subst hb24; subst hb25
  subst hb26; subst hb27; subst hb28; subst hb29; subst hb30; subst hb31
  -- Decompose shared bytes
  rw [hb6, shared_byte_split l0 l1 hl0]
  rw [hb19, shared_byte_split l2 l3 hl2]
  -- Use limb reconstruction lemmas to reduce to linear arithmetic
  have r0 := limb_full_recon l0 hl0
  have r1 := limb_shifted_recon l1 hl1
  have r2 := limb_full_recon l2 hl2
  have r3 := limb_shifted_recon l3 hl3
  have r4 := limb4_recon l4 hl4
  omega
