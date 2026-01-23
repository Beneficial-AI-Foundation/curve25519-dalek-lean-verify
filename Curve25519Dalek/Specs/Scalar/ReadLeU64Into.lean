/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # read_le_u64_into

Specification and proof for `read_le_u64_into`.

This function reads little-endian u64 values into an array.

**Source**: curve25519-dalek/src/scalar.rs:L1349-L1364

## TODO
- Complete proof
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result curve25519_dalek
open scalar

/-- Interpret 8 consecutive bytes of `src` (starting at index 8*i) as a little-endian u64. -/
def le_u64_at (src : Slice U8) (i : Nat) : U64 :=
  core.num.U64.from_le_bytes (Array.make 8#usize [
    src[(8 * i) + 0]!,
    src[(8 * i) + 1]!,
    src[(8 * i) + 2]!,
    src[(8 * i) + 3]!,
    src[(8 * i) + 4]!,
    src[(8 * i) + 5]!,
    src[(8 * i) + 6]!,
    src[(8 * i) + 7]!
  ])

/-- **Spec and proof concerning `scalar.read_le_u64_into`**:
- No panic (always returns successfully) under the length/overflow preconditions
- The output slice has the same length as the input `dst`
- Each output limb is the little-endian u64 decoded from 8 bytes of `src`
-/
@[progress]
theorem read_le_u64_into_spec (src : Slice U8) (dst : Slice U64)
  (h_len : src.length = 8 * dst.length)
  (h_mul : 8 * dst.length ≤ Usize.max) :
  read_le_u64_into src dst ⦃ dst' =>
    dst'.length = dst.length ∧
    (∀ i, i < dst'.length → dst'[i]! = le_u64_at src i) ⦄ := by
  sorry
