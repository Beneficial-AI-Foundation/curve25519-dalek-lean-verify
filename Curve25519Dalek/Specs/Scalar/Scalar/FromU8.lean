/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `Scalar::from(u8)`

Specification and proof for `FromScalarU8::from`.

This function embeds a u8 into a Scalar by writing its little-endian bytes.

**Source**: curve25519-dalek/src/scalar.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.scalar.FromScalarU8

/-
natural language description:

    • Creates a Scalar whose byte representation has x in the least significant byte
      and zeros elsewhere.

natural language specs:

    • The resulting scalar encodes the same numeric value as x
    • The function always succeeds (no panic)
-/

/-- **Spec and proof concerning `scalar.FromScalarU8.from`**:
- No panic (always returns successfully)
- The resulting Scalar encodes the value x
-/
@[progress]
theorem from_spec (x : U8) :
  «from» x ⦃ s => U8x32_as_Nat s.bytes = x.val ⦄ := by
  unfold «from»
  simp [U8x32_as_Nat, Array.update, Array.repeat]
  classical
  let bytes : List U8 := (List.replicate 32 0#u8).set 0 x
  let f : Nat → Nat := fun x_1 =>
    (2 : Nat) ^ (8 * x_1) * (↑(bytes[x_1]?.getD default))
  have hmem : (0 : Nat) ∈ Finset.range 32 := by
    simp
  have hzero : ∀ i ∈ Finset.range 32, i ≠ 0 → f i = 0 := by
    intro i hi hne
    have hi32 : i < 32 := by
      simpa using hi
    have hne' : 0 ≠ i := by
      exact Ne.symm hne
    have hne'' : Nat.not_eq 0 i := by
      exact Or.inl hne'
    have hset : bytes[i]?.getD default = (List.replicate 32 0#u8)[i]?.getD default := by
      have hset? : bytes[i]? = (List.replicate 32 0#u8)[i]? := by
        simpa [bytes] using
          (List.getElem?_set_neq (l := List.replicate 32 0#u8) (i := 0) (j := i) (x := x) hne'')
      simpa using congrArg (fun o => o.getD default) hset?
    have hrep : (List.replicate 32 0#u8)[i]?.getD default = 0#u8 := by
      have hrep' : (List.replicate 32 0#u8)[i]! = 0#u8 := by
        exact List.getElem!_replicate (a := 0#u8) (n := 32) hi32
      simpa [List.getElem!_eq_getElem?_getD] using hrep'
    have hrep_lit : ([0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8][i]?.getD
        default) = 0#u8 := by
      simpa using hrep
    have hget : bytes[i]?.getD default = 0#u8 := by
      simpa [hrep_lit] using hset
    simp [f, hget]
  have hsum : (∑ i ∈ Finset.range 32, f i) = f 0 := by
    exact Finset.sum_eq_single_of_mem 0 hmem hzero
  simpa [f, bytes] using hsum

end curve25519_dalek.scalar.FromScalarU8
