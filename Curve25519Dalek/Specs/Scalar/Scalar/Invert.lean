/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Scalar.Scalar.Unpack
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Zero
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack
/-! # Spec Theorem for `Scalar::invert`

Specification and proof for `Scalar::invert`.

This function computes the multiplicative inverse.

**Source**: curve25519-dalek/src/scalar.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Takes an input Scalar s and returns another Scalar s' that
      represents the multiplicative inverse of s within the underlying
      field \mathbb{Z} / \ell \mathbb{Z}.

natural language specs:

    • \forall Scalars s with s ≠ 0:
      scalar_to_nat(s) * scalar_to_nat(s') is congruent to 1 (mod \ell)
-/

/-- **Spec and proof concerning `scalar.Scalar.invert`**:
- Precondition: The input scalar s must be non-zero (inverting zero has undefined behavior)
- No panic (returns successfully for non-zero input)
- The result s' satisfies the multiplicative inverse property:
  U8x32_as_Nat(s.bytes) * U8x32_as_Nat(s'.bytes) ≡ 1 (mod L)
-/
lemma ZERO_eq : Scalar52_as_Nat backend.serial.u64.scalar.Scalar52.ZERO = 0 := by
  unfold backend.serial.u64.scalar.Scalar52.ZERO backend.serial.u64.scalar.Scalar52.ZERO_body
  decide

@[progress]
theorem invert_spec (s : Scalar) (h : s ≠ ZERO) :
    ∃ s',
    invert s = ok s' ∧
    (U8x32_as_Nat s.bytes * U8x32_as_Nat s'.bytes) ≡ 1 [MOD L]
    := by
  unfold invert
  progress as ⟨ s1, hs1_ok, hs1⟩
  progress as ⟨ s2, hs2⟩
  · intro eq_s1
    simp[eq_s1, ZERO_eq] at hs1
    apply h
    simp [U8x32_as_Nat] at hs1
    simp_all
    apply h
    unfold ZERO ZERO_body eval_global
    simp_all
    cases s with
    | mk bytes =>
      simp_all
      apply Subtype.ext
      apply List.ext_getElem
      · simp_all
      · simp_all
        intro i hi
        have hi_val := hs1 i hi
        interval_cases i
        all_goals simp [Array.repeat, List.replicate]; scalar_tac
  · progress as ⟨ s3, hs3_mod, hs3⟩
    rw[← hs1]
    have := Nat.ModEq.mul_left (Scalar52_as_Nat s1) hs3_mod
    apply Nat.ModEq.trans this hs2

end curve25519_dalek.scalar.Scalar
