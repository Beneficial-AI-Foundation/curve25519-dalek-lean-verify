/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Scalar.Scalar.IsCanonical

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::from_canonical_bytes`

Takes an input array `bytes : [u8; 32]` and tests whether the corresponding scalar
`s = Scalar{bytes}` is canonical, i.e., whether the integer represented by `bytes` lies in
`[0, ℓ − 1]`. Returns `Some(s)` if canonical, `None` otherwise.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

theorem curve25519_dalek.subtle.Choice.ne_zero_iff_eq_one (a : subtle.Choice)
    (h : a ≠ Choice.zero) : a = Choice.one := by
  obtain _ | _ := a.valid
  · exfalso; apply h; cases a; simpa [Choice.zero]
  · cases a; simpa [Choice.one]

namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::from_canonical_bytes`**
• The function always succeeds (no panic)
• If the input bytes are canonical (`U8x32_as_Nat bytes < L`), the result has
  `is_some = Choice.one` and `value.bytes = bytes`
• If the input bytes are non-canonical (`L ≤ U8x32_as_Nat bytes`), the result has
  `is_some = Choice.zero`
-/
@[step]
theorem from_canonical_bytes_spec (bytes : Array U8 32#usize) :
    from_canonical_bytes bytes ⦃ (s : subtle.CtOption Scalar) =>
      (U8x32_as_Nat bytes < L → s.is_some = Choice.one ∧ s.value.bytes = bytes) ∧
      (L ≤ U8x32_as_Nat bytes → s.is_some = Choice.zero) ⦄ := by
  unfold from_canonical_bytes
  step as ⟨_, ha⟩
  step as ⟨_, he, _⟩
  step as ⟨_, _⟩
  step as ⟨_, hd⟩
  step as ⟨f, hf⟩
  step as ⟨_, _, hg⟩
  refine ⟨fun hb ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [ha, high_bit_zero_of_lt_L bytes hb] at he
    simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.lt_add_one, getElem!_pos,
      UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv, iff_true, and_true]; bv_tac
  · simp_all
  · intro _
    rw [hg]
    by_contra h
    have := hd.mp (hf.mp (f.ne_zero_iff_eq_one h)).2
    grind

end curve25519_dalek.scalar.Scalar
