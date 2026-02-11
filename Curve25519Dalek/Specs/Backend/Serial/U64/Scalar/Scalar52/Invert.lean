/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.AsMontgomery
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryInvert
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromMontgomery
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Zero
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR
/-! # Spec Theorem for `Scalar52::invert`

Specification and proof for `Scalar52::invert`.

This function computes the multiplicative inverse.

**Source**: curve25519-dalek/src/scalar.rs
-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64.scalar curve25519_dalek.backend.serial.u64.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar52

set_option linter.style.commandStart false
set_option exponentiation.threshold 260

/-
natural language description:

    • Takes as input an UnpackedScalar u and returns another UnpackedScalar u’ that
      represents the multiplicative inverse of u within the underlying
      field \mathbb{Z} / \ell \mathbb{Z}. This is done by first
      converting u into Montgomery form, then inverting with
      montgomery_invert, and then converting back into UnpackedScalar.

natural language specs:

    • \forall UnpackedScalars u with scalar_to_nat(u) ≢ 0 (mod \ell):
      scalar_to_nat(u) * scalar_to_nat(u') is congruent to 1 (mod \ell)
-/

/-- **Spec and proof concerning `scalar.Scalar52.invert`**:
- Precondition: The unpacked input scalar u must be non-zero modulo L (inverting zero has undefined behavior)
- No panic (returns successfully for non-zero input)
- The result u' satisfies the multiplicative inverse property:
  Scalar52_as_Nat(u) * Scalar52_as_Nat(u') ≡ 1 (mod L)
-/
@[progress]
theorem invert_spec (u : Scalar52) (h : Scalar52_as_Nat u % L ≠ 0) (hu : ∀ i < 5, u[i]!.val < 2 ^ 62) :
    ∃ u', invert u = ok u' ∧
    (Scalar52_as_Nat u * Scalar52_as_Nat u') ≡ 1 [MOD L] := by
  unfold invert
  progress*
  · -- BEGIN TASK
    by_contra _
    have : Scalar52_as_Nat u % L = 0 % L := by
      apply Nat.ModEq.cancel_right_of_coprime (c := R % L) (by try decide)
      try simp_all [Nat.ModEq]
    try simp_all
    -- END TASK
  · -- BEGIN TASK
    rw [Nat.ModEq] at *
    have h := calc (Scalar52_as_Nat u * R) * (Scalar52_as_Nat res * R) % L
        = (Scalar52_as_Nat u * R % L) * (Scalar52_as_Nat res * R % L) % L := by rw [Nat.mul_mod]
      _ = (Scalar52_as_Nat s % L) * (Scalar52_as_Nat s1 % L) % L := by simp only [*]
      _ = R * R % L := by
        simp only [Nat.mul_mod_mod, Nat.mod_mul_mod]
        try simp_all only [ne_eq, Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, getElem!_pos,
          Nat.reducePow]
    have : (Scalar52_as_Nat u * R) * (Scalar52_as_Nat res * R) =
        Scalar52_as_Nat u * Scalar52_as_Nat res * (R * R) := by try grind
    rw [this] at h
    have {a b : ℕ} (h : a * R ^ 2 ≡ b * R ^ 2 [MOD L]) : a ≡ b [MOD L] := by
      have coprime : Nat.Coprime (R ^ 2) L := by try decide
      apply Nat.ModEq.cancel_left_of_coprime (c := R ^ 2) coprime (by try grind)
    exact this h
    -- END TASK

end curve25519_dalek.scalar.Scalar52
