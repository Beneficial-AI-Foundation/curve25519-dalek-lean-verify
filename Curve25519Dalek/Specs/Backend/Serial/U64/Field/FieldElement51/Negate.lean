/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Tactics

/-! # Spec Theorem for `FieldElement51::negate`

Specification and proof for `FieldElement51::negate`.

This function computes the additive inverse (negation) of a field element in 𝔽_p where p = 2^255 - 19.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
Natural language description:

    • Computes the additive inverse of a field element in 𝔽_p where p = 2^255 - 19
    • The field element is represented in radix 2^51 form with five u64 limbs
    • The implementation subtracts each input limb from appropriately chosen constants (= 16*p)
      to avoid underflow and then (weakly) reduces the result modulo p

Natural language specs:

    • The function always succeeds (no panic)
    • For an appropriately bounded field element r, the result r_inv satisfies:
      (Field51_as_Nat(r) + Field51_as_Nat(r_inv)) ≡ 0 (mod p)
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.negate`**:
- No panic (always returns successfully)
- The result r_inv represents the additive inverse of the input r in 𝔽_p, i.e.,
  Field51_as_Nat(r) + Field51_as_Nat(r_inv) ≡ 0 (mod p)
- Requires that input limbs of r are bounded to avoid underflow:
  - Limb 0 must be ≤ 36028797018963664
  - Limbs 1-4 must be ≤ 36028797018963952
  To make the theorem more easily readable and provable, we
-/
@[progress]
theorem negate_spec (r : FieldElement51) (h_bounds : ∀ i, i < 5 → (r[i]!).val < 2 ^ 54) :
    ∃ r_inv, negate r = ok r_inv ∧
    (Field51_as_Nat r + Field51_as_Nat r_inv) % p = 0
    := by
    unfold negate
    progress*
    /- this one is because otherwise we have a chain of similar assertions and we wanna program them away, hence the tactic

    but a model super super human at term mode, my god.

    idee: eliminate the 'code' into math, then simplify math, solve, then loop math into code by improving it



     aeneas's internal comments look like;

     `v_✝¹ : [> let i6 ← Array.index_usize r 3#usize <]  `

    the `try` is so the similar ones can be cleared and the rest of the goals fall out: this is how tactic mode is imperative




    -/
    subst_vars
    -- Discharge bound checks
    all_goals try {
      expand h_bounds with 5
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
        getElem!_pos, Nat.reducePow, Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one,
        ge_iff_le]
      first | omega | scalar_tac | grind
    }

    -- Expand definitions to reveal the arithmetic structure
    unfold Nat.ModEq at *

    -- Use reduction property: sum neg % p = sum pre_neg % p
    rw [Nat.add_mod]
    rw [← neg_post_2]
    rw [← Nat.add_mod]
    clear neg_post_2

    unfold Field51_as_Nat
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, Nat.pow_zero, mul_one]

    -- Reduce Array.make indices
    have id0 : (Array.make 5#usize [i1, i3, i5, i7, i9])[0]! = i1 := by rfl
    have id1 : (Array.make 5#usize [i1, i3, i5, i7, i9])[1]! = i3 := by rfl
    have id2 : (Array.make 5#usize [i1, i3, i5, i7, i9])[2]! = i5 := by rfl
    have id3 : (Array.make 5#usize [i1, i3, i5, i7, i9])[3]! = i7 := by rfl
    have id4 : (Array.make 5#usize [i1, i3, i5, i7, i9])[4]! = i9 := by rfl
    rw [id0, id1, id2, id3, id4]

    -- Substitute variables to get the arithmetic expression
    simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
      getElem!_pos, Nat.reducePow, Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one,
      one_mul, zero_add, Nat.reduceMul]

    -- Prove the sum equals 16 * p
    trans (16 * p) % p
    · congr 1
      simp only [p, Nat.reducePow, Nat.reduceSub, Nat.reduceMul]
      omega
    · simp only [Nat.mul_mod_left]


/-! lean mod support is meh-/
/-
i want it to support verso

assembly should be easy when semantics

what are machines with hardware level good semantics



-/


end curve25519_dalek.backend.serial.u64.field.FieldElement51
