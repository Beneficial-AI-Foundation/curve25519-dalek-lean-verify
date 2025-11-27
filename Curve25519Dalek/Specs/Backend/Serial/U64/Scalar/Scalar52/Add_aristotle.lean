/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

Aristotle failed to load this code into its environment. Double check that the syntax is correct.
Details:
Lean error:
Errors during import; aborting. Details:
input.lean:6:0: error: unknown module prefix 'Curve25519Dalek'

No directory 'Curve25519Dalek' or file 'Curve25519Dalek.olean' in the search path entries:
/code/harmonic-lean/.lake/packages/batteries/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Qq/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/aesop/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/proofwidgets/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/importGraph/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/plausible/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/MD4Lean/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/BibtexQuery/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/UnicodeBasic/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Cli/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/mathlib/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/doc-gen4/.lake/build/lib/lean
/code/harmonic-lean/.lake/build/lib/lean
/workspace/lean4/build/release/stage1/lib/lean
/workspace/lean4/build/release/stage1/lib/lean


-/

/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.mvcgen
import Std.Do
import Std.Tactic.Do
set_option mvcgen.warning false
open Std.Do

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
  sorry

/-! ## mvcgen-based spec theorems

The `@[spec]` attribute tells `mvcgen` to use these theorems when it encounters
calls to `add`. These follow the pattern from Negate.lean.
-/

/-- Spec for add in Triple form, suitable for mvcgen.
    Tagged with @[spec] so mvcgen can use it for calls to add. -/
@[spec]
theorem add_spec_triple (u u' : Scalar52) (Q : PostCond Scalar52 Aeneas.Std.ResultPostShape) :
    ⦃⌜∀ v, Scalar52_as_Nat v = (Scalar52_as_Nat u + Scalar52_as_Nat u') % L →
           (Q.1 v).down⌝⦄
    add u u'
    ⦃Q⦄ := by
  unfold Triple
  intro h_Q
  obtain ⟨v, h_ok, h_mod⟩ := add_spec u u'
  simp only [WP.wp, h_ok, Aeneas.Std.Result.wp_apply_ok]
  exact h_Q v h_mod

/-- User-friendly mvcgen spec for add with modular arithmetic postcondition. -/
@[spec]
theorem add_spec_mvcgen (u u' : Scalar52) :
    ⦃⌜True⌝⦄
    add u u'
    ⦃⇓ v => ⌜Scalar52_as_Nat v = (Scalar52_as_Nat u + Scalar52_as_Nat u') % L⌝⦄ := by
  obtain ⟨v, h_ok, h_mod⟩ := add_spec u u'
  unfold Triple
  intro _htrue
  simp only [WP.wp, h_ok, Aeneas.Std.Result.wp_apply_ok, PostCond.noThrow, ExceptConds.false]
  exact h_mod

/-- Example: using mvcgen on a function that calls add.
    This demonstrates how mvcgen can use the @[spec] lemma. -/
example (a b : Scalar52) :
    ⦃⌜True⌝⦄
    do let sum ← add a b; pure sum
    ⦃⇓ v => ⌜Scalar52_as_Nat v = (Scalar52_as_Nat a + Scalar52_as_Nat b) % L⌝⦄ := by
  mvcgen
  intro v h_mod
  simp only [WP.pure, PostCond.noThrow, ExceptConds.false]
  exact h_mod

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
