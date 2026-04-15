/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang-Liao
-/
import Aeneas
import Curve25519Dalek.Lint.Basic

/-!
# Tests for `linter.curve25519.specIndent`

Tests for the four indentation checks on `@[step]` spec theorems.  Each `#guard_msgs` block
targets exactly one violation so the expected-output annotation stays minimal.

This module docstring includes a `Source:` line so that `linter.curve25519.specSourceDoc`
does **not** fire here.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

-- Two minimal dummy functions for the test cases below.
private def dummyI (n : Nat) : Result Nat := .ok n
private def dummyP (n : Nat) : Result (Nat × Nat) := .ok ⟨n, n⟩

/-! ## Check 1 — continuation binder at wrong column -/

/--
warning: Continuation binder is at column 2, expected 4. Binders that wrap to a new line should be indented 4 spaces per the spec theorem style guide.

Note: This linter can be disabled with `set_option linter.curve25519.specIndent false`
-/
#guard_msgs in
-- Triggers `specIndent` check 1: `(_h : n > 0)` wraps to a new line but uses only 2 spaces.
@[step]
theorem dummyI_binder_wrong_spec (n : Nat)
  (_h : n > 0) :
    dummyI n ⦃ (r : Nat) =>
      r = n ⦄ := by
  simp [dummyI]

-- No warning: binder continuation is correctly at column 4.
#guard_msgs in
@[step]
theorem dummyI_binder_ok_spec (n : Nat)
    (_h : n > 0) :
    dummyI n ⦃ (r : Nat) =>
      r = n ⦄ := by
  simp [dummyI]

/-! ## Check 2 — function application / type after `:` at wrong column -/

/--
warning: The function application / type after `:` is at column 2, expected 4. The type should start on a new line indented 4 spaces per the spec theorem style guide.

Note: This linter can be disabled with `set_option linter.curve25519.specIndent false`
-/
#guard_msgs in
-- Triggers `specIndent` check 2: type is on a new line but only 2 spaces deep.
@[step]
theorem dummyI_type_wrong_spec (n : Nat) :
  dummyI n ⦃ (r : Nat) =>
    r = n ⦄ := by
  simp [dummyI]

-- No warning: type is correctly at column 4.
#guard_msgs in
@[step]
theorem dummyI_type_ok_spec (n : Nat) :
    dummyI n ⦃ (r : Nat) =>
      r = n ⦄ := by
  simp [dummyI]

/-! ## Check 3 — `∧` postcondition RHS at wrong column -/

/--
warning: Postcondition conjunct is at column 8, expected 6. Conjunction operands on new lines should be indented 6 spaces per the spec theorem style guide.

Note: This linter can be disabled with `set_option linter.curve25519.specIndent false`
-/
#guard_msgs in
-- Triggers `specIndent` check 3: the RHS of `∧` is at column 8 (too deep).
@[step]
theorem dummyP_postcond_wrong_spec (n : Nat) :
    dummyP n ⦃ (r : Nat × Nat) =>
      r.1 = n ∧
        r.2 = n ⦄ := by
  simp [dummyP]

-- No warning: ∧ RHS is correctly at column 6.
#guard_msgs in
@[step]
theorem dummyP_postcond_ok_spec (n : Nat) :
    dummyP n ⦃ (r : Nat × Nat) =>
      r.1 = n ∧
      r.2 = n ⦄ := by
  simp [dummyP]

/-! ## Check 4 — proof body after `by` at wrong column -/

/--
warning: Proof body is at column 4, expected 2. Tactics after `by` should be indented 2 spaces per the spec theorem style guide.

Note: This linter can be disabled with `set_option linter.curve25519.specIndent false`
-/
#guard_msgs in
-- Triggers `specIndent` check 4: first tactic is at column 4 instead of 2.
@[step]
theorem dummyI_proof_wrong_spec (n : Nat) :
    dummyI n ⦃ (r : Nat) =>
      r = n ⦄ := by
    simp [dummyI]

-- No warning: proof body is correctly at column 2.
#guard_msgs in
@[step]
theorem dummyI_proof_ok_spec (n : Nat) :
    dummyI n ⦃ (r : Nat) =>
      r = n ⦄ := by
  simp [dummyI]

/-! ## Suppression -/

-- No warning expected: the whole indentation linter is suppressed.
#guard_msgs in
set_option linter.curve25519.specIndent false in
@[step]
theorem dummyI_suppressed_spec (n : Nat)
  (_h : n > 0) :
  dummyI n ⦃ (r : Nat) => r = n ⦄ := by
    simp [dummyI]

/-! ## Fully-correct canonical layout — no warnings at all -/

#guard_msgs in
@[step]
theorem dummyP_canonical_spec (n : Nat)
    (_h : n > 0) :
    dummyP n ⦃ (r : Nat × Nat) =>
      r.1 = n ∧
      r.2 = n ⦄ := by
  simp [dummyP]
