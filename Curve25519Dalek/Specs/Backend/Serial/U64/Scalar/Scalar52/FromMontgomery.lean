/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce

/-! # Spec Theorem for `Scalar52::from_montgomery`

Specification and proof for `Scalar52::from_montgomery`.

This function converts from Montgomery form.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes an input unpacked scalar m in Montgomery form and returns an unpacked scalar u representing
      the value (m * R⁻¹) mod L, where R = 2^260 is the Montgomery constant and L is the group order.
    • This is the inverse operation of as_montgomery.

natural language specs:

    • The function always succeeds (no panic)
    • scalar_to_nat(u) * R = scalar_to_nat(m) mod L
-/

set_option linter.hashCommand false
#setup_aeneas_simps

/-- Strange that this result is required, how can the argument be made smoother where this is used?. -/
theorem set_getElem!_eq (l : List U128) (a : U128) (i : ℕ) (h : i < l.length) :
    (l.set i (a))[i]! = a := by
  simp_all only [List.getElem!_set]

/-- Strange that this result is required, how can the argument be made smoother where this is used?. -/
theorem zero_array (i : ℕ) (hi : i < 9) :
    ((Array.repeat 9#usize 0#u128) : List U128)[i]!.val = 0 := by
  interval_cases i <;> exact rfl

/-- **Spec and proof concerning `from_montgomery_loop`**:
- Specification for the loop that copies limbs from a Scalar52 (5 × U64) into a 9-element U128 array
- Ensures that:
  - The loop always succeeds (no panic)
  - Limbs at indices [i, 5) are copied from the input Scalar52 to the result array
  - Limbs at indices [5, 9) remain unchanged from the input limbs array
  - Limbs at indices [0, i) remain unchanged from the input limbs array
-/
@[progress]
theorem from_montgomery_loop_spec (self : Scalar52) (limbs : Array U128 9#usize) (i : Usize)
    (hi : i.val ≤ 5) :
    ∃ result, from_montgomery_loop self limbs i = ok result ∧
    (∀ j < 5, i.val ≤ j → result[j]! = UScalar.cast .U128 self[j]!) ∧
    (∀ j < 9, 5 ≤ j → result[j]! = limbs[j]!) ∧
    (∀ j < i.val, result[j]! = limbs[j]!) := by
  unfold from_montgomery_loop
  unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  split
  · progress*
    refine ⟨fun j hj hij ↦ ?_, fun j hj hj' ↦ ?_, ?_⟩
    · by_cases hc : i = j
      · rw [res_post_3 j (by simp_all), a_post, i2_post, i1_post, ← hc]
        simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
        apply set_getElem!_eq
        simp; grind
      · exact res_post_1 j hj (by omega)
    · rw [res_post_2 j hj hj']
      have : i ≠ j := by scalar_tac
      simp [*]
    · intro j _
      have := res_post_3 j (by omega)
      simp_all
  · progress*
    have : i.val = 5 := by scalar_tac
    grind
termination_by 5 - i.val
decreasing_by scalar_decr_tac

/-- **Spec and proof concerning `scalar.Scalar52.from_montgomery`**:
- No panic (always returns successfully)
- The result represents the input scalar divided by the Montgomery constant R = 2^260, modulo L
-/
@[progress]
theorem from_montgomery_spec (m : Scalar52) :
    ∃ u, from_montgomery m = ok u ∧
    (Scalar52_as_Nat u * R) % L = Scalar52_as_Nat m % L := by
  unfold from_montgomery
  progress*
  rw [res_post]
  simp only [Scalar52_as_Nat, Scalar52_wide_as_Nat, Finset.sum_range_succ]
  simp [-Nat.reducePow, *, zero_array]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
