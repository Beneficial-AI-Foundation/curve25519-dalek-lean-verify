/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Mathlib.Data.Nat.ModEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Mathlib.Data.Nat.ModEq

/-! # Spec Theorem for `Scalar52::add`

Specification and proof for `Scalar52::add`.

This function adds two elements.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes two input unpacked scalars u and u' and returns an unpacked scalar v representing
      the sum (u + u') mod L where L is the group order.

natural language specs:

    • scalar_to_nat(v) = (scalar_to_nat(u) + scalar_to_nat(u')) mod L
-/

lemma add_loop_spec (u u' : Scalar52)
    (hu : ∀ i, i < 5 → (u[i]!).val < 2 ^ 52)
    (hu' : ∀ i, i < 5 → (u'[i]!).val < 2 ^ 52)
    (mask : U64):
    ∃ sum,
    add_loop mask u u' ZERO 0#u64 0#usize = ok sum ∧
    Scalar52_as_Nat sum = Scalar52_as_Nat u + Scalar52_as_Nat u' ∧
    ∀ i, i < 5 → (sum[i]!).val < 2 ^ 52 := by
    sorry


theorem add_less_than_L_spec (a b : Scalar52)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 52)
    (hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 52)
    :
    let a_nat := Scalar52_as_Nat a;
    let b_nat := Scalar52_as_Nat b;
    (a_nat + b_nat < L) ->
    ∃ v, add a b = ok v ∧ Scalar52_as_Nat v = (L -(b_nat - a_nat) % L)%L
    := by
  intro a_nat b_nat h_lt
  unfold add
  progress*
  obtain ⟨sum, h_sum_ok, h_sum_eq⟩ := add_loop_spec a b ha hb mask
  obtain ⟨h_sum_geq, _⟩ := h_sum_eq
  have h_sub :
    let sum_nat := Scalar52_as_Nat sum;
    ∃ v,
    sub sum constants.L = ok v ∧ Scalar52_as_Nat v = (L -(b_nat - a_nat) % L)%L := by
    sorry
  obtain ⟨v, h_v_ok, h_v_mod⟩ := h_sub
  use v
  constructor
  · rw [h_sum_ok]
    simp [h_v_ok]
  · omega

theorem add_greater_equal_to_L_spec (u u' : Scalar52)
    (hu : ∀ i, i < 5 → (u[i]!).val < 2 ^ 52)
    (hu' : ∀ i, i < 5 → (u'[i]!).val < 2 ^ 52):
    (Scalar52_as_Nat u + Scalar52_as_Nat u' ≥ L) ->
    ∃ v,
    add u u' = ok v ∧
    Scalar52_as_Nat v = (Scalar52_as_Nat u + Scalar52_as_Nat u') % L
    := by
  intro h_geq
  unfold add
  progress*
  -- revert
  obtain ⟨sum, h_sum_ok, h_sum_eq⟩ := add_loop_spec u u' hu hu' mask
  obtain ⟨h_sum_geq, _⟩ := h_sum_eq
  have h_sub :
    let sum_nat := Scalar52_as_Nat sum;
    ∃ v,
    sub sum constants.L = ok v ∧
    (sum_nat ≥ L ∧  Scalar52_as_Nat v = (sum_nat - L) % L) := by
      have h_sum_bounds : ∀ i < 5, (sum[i]!).val < 2 ^ 52 := by
        grind
      have h_L_bounds : ∀ i < 5, (constants.L[i]!).val < 2 ^ 52 := by
        unfold constants.L
        decide
      intro sum_nat
      by_cases sum_lt_L: (sum_nat < L)
      · grind
      · have geq_L: sum_nat ≥ L := by omega
        have scalar_geq : Scalar52_as_Nat sum ≥ Scalar52_as_Nat constants.L := by
          rw [L_spec]
          omega
        obtain ⟨v, h_v_ok, h_v_eq⟩ := sub_spec_geq sum constants.L h_sum_bounds h_L_bounds scalar_geq
        use v
        constructor
        · rw [h_v_ok]
        · constructor
          · omega
          · rw [L_spec] at h_v_eq
            omega
  obtain ⟨v, h_v_ok, h_v_mod⟩ := h_sub
  use v
  constructor
  · rw [h_sum_ok]
    simp [h_v_ok]
  · rw [← h_sum_geq]
    obtain ⟨sum_geq_l, h_eq⟩ := h_v_mod
    rw [← Nat.mod_eq_sub_mod] at h_eq; all_goals omega

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- No panic (always returns successfully)
- The result represents the sum of the two input scalars modulo L
-/
@[progress]
theorem add_spec (u u' : Scalar52)
    (hu : ∀ i, i < 5 → (u[i]!).val < 2 ^ 52)
    (hu' : ∀ i, i < 5 → (u'[i]!).val < 2 ^ 52):
    ∃ v,
    add u u' = ok v ∧
    Scalar52_as_Nat v = (Scalar52_as_Nat u + Scalar52_as_Nat u') % L
    := by
  sorry
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
