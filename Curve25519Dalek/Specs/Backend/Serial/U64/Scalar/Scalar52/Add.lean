/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Mathlib.Data.Nat.ModEq
-- import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
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
@[progress]
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 52)
    (hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 52) :
    ∃ result, sub a b = ok result ∧
    Scalar52_as_Nat result = (Scalar52_as_Nat a - Scalar52_as_Nat b) % L := by
  sorry

lemma add_loop_spec (u u' : Scalar52)
    (hu : ∀ i, i < 5 → (u[i]!).val < 2 ^ 52)
    (hu' : ∀ i, i < 5 → (u'[i]!).val < 2 ^ 52)
    (mask : U64):
    ∃ sum,
    add_loop mask u u' ZERO 0#u64 0#usize = ok sum ∧
    Scalar52_as_Nat sum = Scalar52_as_Nat u + Scalar52_as_Nat u' ∧
    ∀ i, i < 5 → (sum[i]!).val < 2 ^ 52 := by
    sorry
    -- progress*


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
  unfold add
  progress*
  obtain ⟨sum, h_sum_ok, h_sum_eq⟩ := add_loop_spec u u' hu hu' mask
  have h_sub : ∃ v,
    sub sum constants.L = ok v
    ∧ Scalar52_as_Nat v = (Scalar52_as_Nat sum - Scalar52_as_Nat constants.L) % L := by
      have h_sum_bounds : ∀ i < 5, (sum[i]!).val < 2 ^ 52 := by
        grind
      have h_L_bounds : ∀ i < 5, (constants.L[i]!).val < 2 ^ 52 := by
        unfold constants.L
        decide
      exact sub_spec sum constants.L h_sum_bounds h_L_bounds
  obtain ⟨v, h_v_ok, h_v_mod⟩ := h_sub
  use v
  constructor
  · rw [h_sum_ok]
    simp [h_v_ok]
  · rw [h_v_mod]
    have h_mod_eq : (Scalar52_as_Nat sum - Scalar52_as_Nat constants.L) % L  =
    Scalar52_as_Nat sum % L  := by
      sorry
      -- Cannot prove this since sub_spec seems to be incorrect. It does not specify when a < b, how does 'sub a b' behaves.
      -- by_cases sum_lt_L: (Scalar52_as_Nat sum < L)
      -- · sorry
      -- · rw [curve25519_dalek.backend.serial.u64.L_spec]
      --   rw [← Nat.mod_eq_sub_mod]
      --   omega
    grind
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
