/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Tactics
import Curve25519Dalek.Aux

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 3000000

/-! # Spec Theorem for `Scalar52::add`

Specification and proof for `Scalar52::add`.

This function adds two elements.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-- Auxiliary definition to interpret a vector of `j` u64 limbs as a number (52-bit limbs) -/
def U64x5_slice_as_Nat_add (limbs : Array U64 5#usize) (j : Nat) : Nat :=
  ∑ i ∈ Finset.range j, 2^(52 * i) * (limbs[i]!).val

@[simp]
theorem U64x5_slice_as_Nat_add_zero (limbs : Array U64 5#usize) :
    U64x5_slice_as_Nat_add limbs 0 = 0 := by
  simp [U64x5_slice_as_Nat_add]

/-- Convenience theorem unfolding one more limb in `U64x5_slice_as_Nat_add`. -/
@[simp]
theorem U64x5_slice_as_Nat_add_succ (limbs : Array U64 5#usize) (j : Nat) :
    U64x5_slice_as_Nat_add limbs (j.succ) =
      U64x5_slice_as_Nat_add limbs j + 2^(52 * j) * (limbs[j]!).val := by
  have h :=
    Finset.sum_range_succ (fun i => 2^(52 * i) * (limbs[i]!).val) j
  simpa [U64x5_slice_as_Nat_add, add_comm, add_left_comm, add_assoc]
    using h

/-- **Spec for `backend.serial.u64.scalar.Scalar52.add_loop`**:
- The loop adds two arrays limb by limb with carry propagation
- After processing i limbs: U64x5_slice_as_Nat_add sum' i ≡ U64x5_slice_as_Nat_add a i + U64x5_slice_as_Nat_add b i + carry*2^(52*i) [MOD 2^(52*i)]
- When i = 5, this gives: Scalar52_as_Nat sum' ≡ Scalar52_as_Nat a + Scalar52_as_Nat b [MOD 2^260]
-/
@[progress]
theorem add_loop_spec (mask : U64) (a b sum : Array U64 5#usize) (carry : U64) (i : Usize)
    (ha : ∀ j, j < 5 → (a[j]!).val < 2 ^ 52) (hb : ∀ j, j < 5 → (b[j]!).val < 2 ^ 52)
    (hs : ∀ j, j < i.val → (sum[j]!).val < 2 ^ 52)
    (hs_rest : ∀ j, i.val ≤ j → j < 5 → (sum[j]!).val = 0)
    (hmask : mask.val = 2 ^ 52 - 1)
    (hi : i.val ≤ 5)
    (hmod : U64x5_slice_as_Nat_add sum i ≡
      U64x5_slice_as_Nat_add a i + U64x5_slice_as_Nat_add b i + carry.val * 2 ^ (52 * i.val)
        [MOD 2 ^ (52 * i.val)]) :
    ∃ sum', add_loop mask a b sum carry i = ok sum' ∧
    U64x5_slice_as_Nat_add sum' i ≡
      U64x5_slice_as_Nat_add a i + U64x5_slice_as_Nat_add b i + carry.val * 2 ^ (52 * i.val)
        [MOD 2 ^ (52 * i.val)] ∧
    (∀ j, j < 5 → (sum'[j]!).val < 2 ^ 52)
    := by
  unfold add_loop
  by_cases hlt : i < 5#usize
  · have hi_lt : i.val < 5 := by simpa using hlt
    -- Recursive branch to be completed.
    sorry
  · have hnot : ¬ i.val < 5 := by
      simpa using hlt
    have hge : 5 ≤ i.val := Nat.le_of_not_lt hnot
    have hi_eq : i.val = 5 := Nat.le_antisymm hi hge
    refine ⟨sum, ?_, ?_, ?_⟩
    · simp [hlt]
    · simpa using hmod
    · intro j hj
      have : j < i.val := by simpa [hi_eq]
      exact hs j this

/-
natural language description:

    • Takes two input unpacked scalars u and u' and returns an unpacked scalar v representing
      the sum (u + u') mod L where L is the group order.

natural language specs:

    • scalar_to_nat(v) = (scalar_to_nat(u) + scalar_to_nat(u')) mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- No panic (always returns successfully)
- The result represents the sum of the two input scalars modulo L
-/
@[progress]
theorem add_spec (u u' : Scalar52) :
    ∃ v,
    add u u' = ok v ∧
    Scalar52_as_Nat v = (Scalar52_as_Nat u + Scalar52_as_Nat u') % L
    := by
  unfold add
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
