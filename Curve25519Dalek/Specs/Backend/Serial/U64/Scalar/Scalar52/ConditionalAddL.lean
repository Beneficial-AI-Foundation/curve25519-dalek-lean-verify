/-
Copyright 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L

/-! # Spec Theorem for `Scalar52::conditional_add_l`

This function conditionally adds the group order L to a scalar based on a choice parameter.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

## Rust source

```rust
pub(crate) fn conditional_add_l(&mut self, condition: Choice) -> u64 {
    let mut carry: u64 = 0;
    let mask = (1u64 << 52) - 1;

    let mut i = 0;
    while i < 5 {
        let addend = u64::conditional_select(&0, &constants::L[i], condition);
        carry = (carry >> 52) + self[i] + addend;
        self[i] = carry & mask;
        i += 1;
    }

    carry
}
```

## Proof overview

The function iterates over 5 limbs, at each step computing:

```rust
carry' = (carry >> 52) + self[i] + addend
self[i] = carry' & mask
```

where `addend = L[i]` if `condition=1` or `0` otherwise, and `mask = 2^52 - 1`.

**No overflow**: The key invariant is `carry < 2^53` at each iteration.
This follows from the precondition `self[i] < 2^52` and the fact that `L[i] < 2^52`:
  `carry >> 52 < 2`  (since carry < 2^53)
  `self[i]     < 2^52`
  `addend      ≤ L[i] < 2^52`
  `total       < 2 + 2^52 + 2^52 < 2^53 < 2^64`
Without the bound `self[i] < 2^52`, the addition could overflow u64.

**Value invariant**: After processing limb i, the loop maintains:
```
  Scalar52_as_Nat(self') + 2^(52*(i+1)) * (carry'/2^52)
    = Scalar52_as_Nat(self_orig) + condition * Σ_{j < i+1} 2^(52*j) * L[j]
         + 2^(52*0) * (carry_init/2^52)
```
This follows from the standard radix-2^52 addition with carry propagation:
each `self[i] = carry' mod 2^52` stores the low bits, while `carry'/2^52`
propagates to the next limb.

After all 5 limbs, the full sum telescopes to:
```
  Scalar52_as_Nat(result) + 2^260 * (carry_final/2^52)
    = Scalar52_as_Nat(self) + condition * Scalar52_as_Nat(L)
```

**Natural language spec**:

    • Input: limbs bounded by 2^52
    • If condition is 1 and input ∈ [2^260 - L, 2^260):
        - Output value: u' + 2^260 = u + L
        - Output canonical: u' < L
        - Output limbs: < 2^52
    • If condition is 0:
        - Output value: u' = u
        - Output limbs: < 2^52
    • Carry value: not used by caller

-/

set_option linter.hashCommand false
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow
set_option exponentiation.threshold 260

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

@[progress]
theorem conditional_add_l_loop_spec (self : Scalar52) (condition : subtle.Choice)
    (carry : U64) (mask : U64) (i : Usize) (hself : ∀ j < 5, self[j]!.val < 2 ^ 52)
    (hmask : mask.val = 2 ^ 52 - 1) (hi : i.val ≤ 5) (hcarry : carry.val < 2 ^ 53) :
    conditional_add_l_loop self condition carry mask i ⦃ (result : U64 × Scalar52) =>
      (∀ j < 5, result.2[j]!.val < 2 ^ 52) ∧
      (Scalar52_as_Nat result.2 + 2 ^ 260 * (result.1.val / 2 ^ 52) =
        Scalar52_as_Nat self + (if condition = Choice.one then Scalar52_as_Nat constants.L else 0) +
        2 ^ (52 * i.val) * (carry.val / 2 ^ 52) -
        (if condition = Choice.one then ∑ j ∈ Finset.Ico 0 i.val, 2 ^ (52 * j) * constants.L[j]!.val
          else 0)) ⦄ := by
  unfold conditional_add_l_loop
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  split
  case isTrue hlt =>
    have hi' : i.val < 5 := by grind
    have hself_i : self[i.val]!.val < 2 ^ 52 := hself i.val hi'
    have hL_i : constants.L[i.val]!.val < 2 ^ 52 := constants.L_limbs_spec i hi'
    progress as ⟨i1, hi1⟩  -- L[i]
    progress as ⟨addend, haddend_one, haddend_zero⟩  -- conditional_select
    have hi1_eq : i1.val = constants.L[i.val]!.val := by simp [hi1]
    have haddend_bound : addend.val < 2 ^ 52 := by
      cases Choice.eq_zero_or_one condition with
      | inl h => have := haddend_zero h; subst this; decide
      | inr h => have := haddend_one h; subst this; omega
    progress as ⟨i2, hi2⟩  -- carry >>> 52
    have hi2_bound : i2.val < 2 := by simp [hi2, Nat.shiftRight_eq_div_pow]; omega
    progress as ⟨i3, hi3⟩  -- self[i]
    have hi3_eq : i3.val = self[i.val]!.val := by simp [hi3]
    have hi3_bound : i3.val < 2 ^ 52 := by rw [hi3_eq]; exact hself_i
    have hi2i3_ok : i2.val + i3.val < 2 ^ 64 := by omega
    progress as ⟨i4, hi4⟩  -- i2 + i3
    have hi4_bound : i4.val < 2 ^ 52 + 2 := by simp [hi4]; omega
    have hi4addend_ok : i4.val + addend.val < 2 ^ 64 := by omega
    progress as ⟨carry1, hcarry1⟩  -- i4 + addend
    have hcarry1_bound : carry1.val < 2 ^ 53 := by simp [hcarry1]; omega
    progress as ⟨_, index_mut_back, h_imb, _⟩  -- index_mut
    progress as ⟨i5, hi5⟩  -- carry1 &&& mask
    have hi5_mod : i5.val = carry1.val % 2 ^ 52 := by
      simp [hi5, UScalar.val_and, hmask]
    have hi5_bound : i5.val < 2 ^ 52 := by rw [hi5_mod]; exact Nat.mod_lt _ (by omega)
    have hi_plus1_ok : i.val + 1 < 2 ^ 64 := by omega
    progress as ⟨i6, hi6⟩  -- i + 1
    have hi6_bound : i6.val ≤ 5 := by grind
    have hself1_limbs : ∀ j < 5, (Aeneas.Std.Array.set self i i5)[j]!.val < 2 ^ 52 := by
      intro j hj
      by_cases hjc : j = i.val
      · rw [hjc]
        have := Array.set_of_eq self i5 i (by grind)
        simp only [UScalar.ofNat_self_val, Array.getElem!_Nat_eq, Array.set_val_eq] at this ⊢
        simpa [this]
      · have := Array.set_of_ne self i5 j i (by grind) (by grind) (by omega)
        have := hself j hj
        clear haddend_one haddend_zero
        simp_all
    rw [← h_imb] at hself1_limbs
    progress as ⟨res, hres_limbs, hres_inv⟩
    refine ⟨hres_limbs, ?_⟩
    rw [h_imb] at hres_inv
    simp only [hi6] at hres_inv
    have hcarry1_expand : carry1.val = carry.val / 2 ^ 52 + self[i.val]!.val + addend.val := by
      simp [hcarry1, hi4, hi2, Nat.shiftRight_eq_div_pow, hi3_eq]
    have hcarry1_split : i5.val + 2 ^ 52 * (carry1.val / 2 ^ 52) = carry1.val := by
      rw [hi5_mod]; have := Nat.mod_add_div carry1.val (2 ^ 52); omega
    have hpow_split : 2 ^ (52 * (i.val + 1)) = 2 ^ (52 * i.val) * 2 ^ 52 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have hself1_nat : Scalar52_as_Nat (Aeneas.Std.Array.set self i i5) =
        Scalar52_as_Nat self - 2 ^ (52 * i.val) * self[i.val]!.val + 2 ^ (52 * i.val) * i5.val := by
      clear haddend_one haddend_zero haddend_bound hres_inv hres_limbs res
      unfold Scalar52_as_Nat
      have h_acc : ∀ j, j < 5 → (Aeneas.Std.Array.set self i i5)[j]!.val =
          if j = i.val then i5.val else self[j]!.val := by
        intro j _
        by_cases j = i.val <;> simp [*]
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      interval_cases i.val <;> simp (config := { decide := true }) only [h_acc 0 (by omega),
        h_acc 1 (by omega), h_acc 2 (by omega), h_acc 3 (by omega), h_acc 4 (by omega),
        ite_true, ite_false] <;> omega
    have : ∑ j ∈ Finset.Ico 0 (i.val + 1), 2 ^ (52 * j) * constants.L[j]!.val =
        ∑ j ∈ Finset.Ico 0 i.val, 2 ^ (52 * j) * constants.L[j]!.val +
        2 ^ (52 * i.val) * constants.L[i.val]!.val := by
      rw [Finset.sum_Ico_succ_top (Nat.zero_le i.val)]
    -- Case split on condition to resolve if-then-else in the value invariant
    cases Choice.eq_zero_or_one condition with
    | inl hc0 =>
      have haddend_val : addend.val = 0 := by
        have := haddend_zero hc0; subst this; rfl
      simp only [hc0, Choice.zero_ne_one, reduceIte, ↓reduceIte] at hres_inv ⊢
      have : 2 ^ (52 * i.val) * i5.val + 2 ^ (52 * i.val) * 2 ^ 52 * (carry1.val / 2 ^ 52) =
          2 ^ (52 * i.val) * carry1.val := by grind
      have : 2 ^ (52 * i.val) * carry1.val = 2 ^ (52 * i.val) * (carry.val / 2 ^ 52) +
          2 ^ (52 * i.val) * self[i.val]!.val := by
        have : addend.val = 0 := haddend_val; grind
      rw [hself1_nat, hpow_split] at hres_inv
      have := Scalar52_limb_le_nat self i.val hi'
      omega
    | inr hc1 =>
      have haddend_val : addend.val = constants.L[i.val]!.val := by
        have := haddend_one hc1; subst this; exact hi1_eq
      simp only [hc1, reduceIte] at hres_inv ⊢
      rw [hpow_split] at hres_inv
      have : 2 ^ (52 * i.val) * i5.val + 2 ^ (52 * i.val) * 2 ^ 52 * (carry1.val / 2 ^ 52) =
          2 ^ (52 * i.val) * carry1.val := by grind
      have : 2 ^ (52 * i.val) * carry1.val =
          2 ^ (52 * i.val) * (carry.val / 2 ^ 52) + 2 ^ (52 * i.val) * self[i.val]!.val +
          2 ^ (52 * i.val) * constants.L[i.val]!.val := by
        have : addend.val = constants.L[i.val]!.val := haddend_val; grind
      have := Scalar52_limb_le_nat self i.val hi'
      omega
  case isFalse hge =>
    have : i.val = 5 := by grind
    progress*
    refine ⟨by assumption, ?_⟩
    have : ∑ j ∈ Finset.Ico 0 5, 2 ^ (52 * j) * constants.L[j]!.val =
        Scalar52_as_Nat constants.L := by simp [Scalar52_as_Nat]
    cases Choice.eq_zero_or_one condition with
    | inl h => simp [*]
    | inr h => grind
termination_by 5 - i.val
decreasing_by grind

/-- **Spec for `scalar.Scalar52.conditional_add_l`**
- Requires input limbs bounded by 2^52
- When condition is 1, requires input value in [2^260 - L, 2^260)
- When condition is 1: result + 2^260 = input + L, with result < L and limbs < 2^52
- When condition is 0: result unchanged with limbs < 2^52
-/
@[progress]
theorem conditional_add_l_spec (self : Scalar52) (condition : subtle.Choice)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (hself' : condition = Choice.one → 2 ^ 260 ≤ Scalar52_as_Nat self + L)
    (hself'' : condition = Choice.one → Scalar52_as_Nat self < 2 ^ 260)
    (hself''' : condition = Choice.zero → Scalar52_as_Nat self < L) :
    conditional_add_l self condition ⦃ (result : U64 × Scalar52) =>
      (∀ i < 5, result.2[i]!.val < 2 ^ 52) ∧
      (Scalar52_as_Nat result.2 < L) ∧
      (condition = Choice.one → Scalar52_as_Nat result.2 + 2 ^ 260 = Scalar52_as_Nat self + L) ∧
      (condition = Choice.zero → Scalar52_as_Nat result.2 = Scalar52_as_Nat self) ⦄ := by
  unfold conditional_add_l
  progress*
  rw [constants.L_spec] at *
  refine ⟨by assumption, ?_, ?_, ?_⟩
  · -- result < L
    cases Choice.val_eq_zero_or_one condition with
    | inl =>
      have := Choice.eq_zero_of_val condition (by assumption)
      have : Scalar52_as_Nat result.2 + 2 ^ 260 * (result.1.val / 2 ^ 52) =
          Scalar52_as_Nat self := by simp [*]
      grind
    | inr =>
      have := Choice.eq_one_of_val condition (by assumption)
      have : Scalar52_as_Nat result.2 < 2 ^ 260 := Scalar52_as_Nat_bounded result.2 (by assumption)
      grind [Finset.Ico_self]
  · -- condition = Choice.one case
    have : Scalar52_as_Nat result.2 < 2 ^ 260 := Scalar52_as_Nat_bounded result.2 (by assumption)
    grind [Finset.Ico_self, L_lt]
  · -- condition = Choice.zero case
    intro _
    have : Scalar52_as_Nat result.2 + 2 ^ 260 * (result.1.val / 2 ^ 52) = Scalar52_as_Nat self := by
      simp [*]
    grind [L_lt]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
