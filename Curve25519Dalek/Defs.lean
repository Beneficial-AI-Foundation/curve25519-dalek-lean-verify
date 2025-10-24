import Aeneas
import Curve25519Dalek.Funs
import Mathlib

/-! # Definitions

Common definitions used across spec theorems.
-/

open Aeneas.Std Result
open curve25519_dalek

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Constants -/

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

/-- The group order L for Scalar52 arithmetic -/
def L : Nat := 2^252 + 27742317777372353535851937790883648493

/-- The Montgomery constant R = 2^260 used for Scalar52 Montgomery form conversions -/
def R : Nat := 2^260

/-- The cofactor of curve25519 -/
@[simp]
def h : Nat := 8

/-! ## Auxiliary definitions for interpreting arrays as natural numbers -/

/-- Auxiliary definition to interpret a vector of u64 limbs as a natural number (51-bit limbs) -/
@[simp]
def U64x5_as_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).val

/-- Auxiliary definition to interpret a 9-element u128 array as a natural number.
This represents the result of polynomial multiplication where each limb is at position 51*i bits. -/
@[simp]
def U128x9_as_Nat (limbs : Array U128 9#usize) : Nat :=
  ∑ i ∈ Finset.range 9, 2^(51 * i) * (limbs[i]!).val

/-- Auxiliary definition to interpret a byte array as a natural number (little-endian) -/
@[simp]
def U8x32_as_Nat (bytes : Array U8 32#usize) : Nat :=
  ∑ i ∈ Finset.range 32, 2^(8 * i) * (bytes[i]!).val

/-- Auxiliary definition to interpret a wide byte array (64 bytes) as a natural number (little-endian) -/
@[simp]
def U8x64_as_Nat (bytes : Array U8 64#usize) : Nat :=
  ∑ i ∈ Finset.range 64, 2^(8 * i) * (bytes[i]!).val
