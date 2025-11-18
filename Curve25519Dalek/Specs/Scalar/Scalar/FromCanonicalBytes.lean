/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Scalar.Scalar.IsCanonical

/-! # Spec Theorem for `Scalar::from_canonical_bytes`

Specification and proof for `Scalar::from_canonical_bytes`.

This function constructs a scalar from canonical bytes.

Source: curve25519-dalek/src/scalar.rs -/

theorem curve25519_dalek.subtle.Choice.ne_zero_iff_eq_one (a : subtle.Choice) (h : a ≠ Choice.zero) : a = Choice.one := by
  obtain h' | h' := a.valid
  · exfalso
    apply h
    cases a
    simpa [Choice.zero]
  · cases a
    simpa [Choice.one]

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-- If a 32-byte array represents a value less than `2 ^ 252`, then the high bit (bit 7) of byte 31
must be 0. -/
theorem high_bit_zero_of_lt_255 (b : Array U8 32#usize) (h : U8x32_as_Nat b < 2 ^ 255) :
    (b[31]!).val >>> 7 = 0 := by
  by_contra!
  have : 2 ^ 7 ≤ b[31]!.val := by omega
  have : 2 ^ 255 ≤ U8x32_as_Nat b := by
    unfold U8x32_as_Nat
    have : ∑ i ∈ Finset.range 32, 2^(8*i) * (b[i]!).val =
        ∑ i ∈ Finset.range 31, 2^(8*i) * (b[i]!).val + 2^(8*31) * (b[31]!).val := by
      rw [Finset.sum_range_succ]
    grind
  omega

/-- If a 32-byte array represents a value less than `L`, then the high bit (bit 7) of byte 31
must be 0. -/
theorem high_bit_zero_of_lt_L (b : Array U8 32#usize) (h : U8x32_as_Nat b < L) :
    (b[31]!).val >>> 7 = 0 := by
  refine high_bit_zero_of_lt_255 b ?_
  have : L ≤ 2 ^ 255 := by decide
  grind
/-- If a 32-byte array represents a value less than `L`, then the high bit (bit 7) of byte 31
must be 0. -/

theorem high_bit_zero_of_lt_L' (b : Array U8 32#usize) (h : U8x32_as_Nat b < L) :
    ((b : List U8)[31]!).val >>> 7 = 0 := by
  have : L ≤ 2 ^ 255 := by decide
  have := high_bit_zero_of_lt_255 b (show U8x32_as_Nat b < 2 ^ 255 by grind )
  simp_all

/-
natural language description:

    • Takes an input array b of type [u8;32].

      The condition checked is whether the Scalar s = Scalar{b} corresponding to the input array
      fulfils s.is_canonical(), which means that the number represented by b lies in [0, \ell - 1].

      If this condition is true, then the Scalar s is returned,
      otherwise None is returned.

natural language specs:

    • If u8x32_to_nat(b) < \ell \then s = Scalar{b} else s = None
-/

/-- **Spec and proof concerning `scalar.Scalar.from_canonical_bytes`**:
- No panic (always returns successfully)
- When the input bytes represent a canonical value (< L), the function returns a CtOption Scalar
  where is_some = Choice.one and the scalar's byte representation equals the input bytes
- When the input bytes represent a non-canonical value (≥ L), the function returns a CtOption Scalar
  where is_some = Choice.zero (i.e., None)
-/
@[progress]
theorem from_canonical_bytes_spec (b : Array U8 32#usize) :
    ∃ s, from_canonical_bytes b = ok s ∧
    (U8x32_as_Nat b < L → s.is_some = Choice.one ∧ s.value.bytes = b) ∧
    (L ≤ U8x32_as_Nat b → s.is_some = Choice.zero) := by
  unfold from_canonical_bytes
  progress as ⟨_, ha⟩
  progress as ⟨_, he, _⟩
  progress as ⟨_, _⟩
  progress as ⟨_, hd⟩
  progress as ⟨f, hf⟩
  progress as ⟨_, _, hg⟩
  refine ⟨fun hb ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [ha, high_bit_zero_of_lt_L' b hb] at he
    simp_all; bv_tac
  · simp_all
  · intro _
    rw [hg]
    by_contra h
    have := hd.mp (hf.mp (f.ne_zero_iff_eq_one h)).2
    grind

end curve25519_dalek.scalar.Scalar
