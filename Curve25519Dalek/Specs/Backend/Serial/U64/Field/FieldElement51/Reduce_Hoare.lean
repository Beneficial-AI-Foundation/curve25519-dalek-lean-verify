/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/

import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
import Mathlib
import Curve25519Dalek.mvcgen
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Std.Do
import Std.Tactic.Do
open Std.Do

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000

/-! # Reduce Hoare Spec

Hoare-style specification for `reduce`, derived from `reduce_spec`.
-/

open Aeneas.Std Result
open curve25519_dalek
open backend.serial.u64.field.FieldElement51
open reduce

/-! ## Hoare Spec for `reduce` -/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.reduce`**:
- Does not overflow and hence returns a result
- All the limbs of the result are small, ≤ 2^(51 + ε)
- The result is equal to the input mod p. -/

@[spec]
theorem reduce_hoare_spec (limbs : Array U64 5#usize) :
⦃⌜True⌝⦄
reduce limbs
⦃⇓result => ⌜(∀ i, i < 5 → (result[i]!).val ≤ 2^51 + (2^13 - 1) * 19) ∧ Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p]⌝⦄ := by
  simp only [Std.Do.Triple, Std.Do.wp]
  intro _
  have h := reduce_spec limbs
  obtain ⟨result, hok, hbounds, hmod⟩ := h
  simp only [Aeneas.Std.Result.wp, hok]
  exact ⟨hbounds, hmod⟩
