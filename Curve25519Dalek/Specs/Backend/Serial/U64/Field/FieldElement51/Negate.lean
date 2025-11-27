/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alok Singh
-/
import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.mvcgen
import Std.Do
import Std.Tactic.Do
set_option mvcgen.warning false
open Std.Do

/-! # Spec Theorem for `FieldElement51::negate`

Specification and proof for `FieldElement51::negate`.

This function computes the additive inverse (negation) of a field element in 𝔽_p where p = 2^255 - 19.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
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
- All the limbs of the result are small, ≤ 2^(51 + ε)
- Requires that input limbs of r are bounded to avoid underflow:
  - Limb 0 must be ≤ 36028797018963664
  - Limbs 1-4 must be ≤ 36028797018963952
  To make the theorem more readable we use a single bound for all limbs. -/
@[progress]
theorem negate_spec (r : FieldElement51) (h : ∀ i < 5, r[i]!.val < 2 ^ 54) :
    ∃ r_inv, negate r = ok r_inv ∧
    (Field51_as_Nat r + Field51_as_Nat r_inv) % p = 0 ∧
    (∀ i < 5, r_inv[i]!.val ≤ 2^51 + (2^13 - 1) * 19) := by
  unfold negate
  progress*
  · have := h 0 (by simp); simp_all; grind
  · have := h 1 (by simp); simp_all; grind
  · have := h 2 (by simp); simp_all; grind
  · have := h 3 (by simp); simp_all; grind
  · have := h 4 (by simp); simp_all; grind
  constructor
  · have : 16 * p =
      36028797018963664 * 2^0 +
      36028797018963952 * 2^51 +
      36028797018963952 * 2^102 +
      36028797018963952 * 2^153 +
      36028797018963952 * 2^204 := by simp [p]
    simp_all [Nat.ModEq, Field51_as_Nat, Finset.sum_range_succ, Array.make, Array.getElem!_Nat_eq]
    grind
  · assumption


/- TODO impl OfNat and OfScientific for `FieldElement51` -/

/-! ## mvcgen-based spec theorem

The `@[spec]` attribute tells `mvcgen` to use this theorem when it encounters
calls to `negate`. The precondition encodes the wp transformer of the function body.
-/

/-- Spec for negate in Triple form, suitable for mvcgen.
    Tagged with @[spec] so mvcgen can use it for calls to negate.

    This follows the pattern from Std.Do.Triple.SpecLemmas:
    - Precondition includes bounds check AND continuation condition
    - Postcondition is the generic Q passed in

    Note: For ResultPostShape, `Assertion` = `ULift Prop`, so we use `.down` to extract the Prop. -/
@[spec]
theorem negate_spec_triple (r : FieldElement51) (Q : PostCond FieldElement51 Aeneas.Std.ResultPostShape) :
    ⦃⌜(∀ i < 5, (r[i]!).val < 2 ^ 54) ∧
      (∀ r_inv, (Field51_as_Nat r + Field51_as_Nat r_inv) % p = 0 →
                (∀ i < 5, r_inv[i]!.val ≤ 2^51 + (2^13 - 1) * 19) →
                (Q.1 r_inv).down)⌝⦄
    negate r
    ⦃Q⦄ := by
  -- Prove using the existing negate_spec
  unfold Triple
  intro ⟨h_bounds, h_Q⟩
  -- Get the result from negate_spec
  obtain ⟨r_inv, h_ok, h_mod, h_limbs⟩ := negate_spec r h_bounds
  -- Show wp⟦negate r⟧ Q
  simp only [WP.wp, h_ok, Aeneas.Std.Result.wp_apply_ok]
  exact h_Q r_inv h_mod h_limbs

/-- User-friendly spec with precondition bounds and modular arithmetic postcondition. -/
@[spec]
theorem negate_spec' (r : FieldElement51) (h_bounds : ∀ i < 5, (r[i]!).val < 2 ^ 54) :
⦃⌜True⌝⦄
negate r
⦃⇓ r_inv => ⌜(Field51_as_Nat r + Field51_as_Nat r_inv) % p = 0⌝⦄
    := by
    -- Use the negate_spec result directly
    obtain ⟨r_inv, h_ok, h_mod, _⟩ := negate_spec r h_bounds
    unfold Triple
    intro _htrue
    simp only [WP.wp, h_ok, Aeneas.Std.Result.wp_apply_ok, PostCond.noThrow, ExceptConds.false]
    exact h_mod

/-- Example: using mvcgen on a function that calls negate.
    This demonstrates how mvcgen can use the @[spec] lemma. -/
example (r : FieldElement51) (h : ∀ i < 5, (r[i]!).val < 2 ^ 54) :
    ⦃⌜True⌝⦄
    do let res ← negate r; pure res
    ⦃⇓ r_inv => ⌜(Field51_as_Nat r + Field51_as_Nat r_inv) % p = 0⌝⦄ := by
  -- mvcgen uses @[spec] negate_spec_triple to handle the negate call
  mvcgen
  -- VC after mvcgen: bounds ∧ continuation
  constructor
  · -- Bounds: ∀ i < 5, r[i]! < 2^54
    exact h
  · -- Continuation: ∀ r_inv, spec_props → wp⟦pure r_inv⟧ Q
    intro r_inv h_mod _h_limbs
    -- Goal: ((wp (pure r_inv)).apply (PostCond.noThrow ...)).down
    -- Simplify wp of pure
    simp only [WP.pure, PostCond.noThrow, ExceptConds.false]
    exact h_mod


end curve25519_dalek.backend.serial.u64.field.FieldElement51
