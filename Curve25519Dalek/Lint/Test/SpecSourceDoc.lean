/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang-Liao
-/
import Aeneas
import Curve25519Dalek.Lint.Basic

/-!
# Tests for `linter.curve25519.specSourceDoc`

This module-level docstring deliberately omits the Rust-origin attribution line that the
style guide requires.  That omission is what allows the `specSourceDoc` linter to fire in
the test cases below.

`specStep` and `specSuffix` do not fire here because every test theorem either has both
`@[step]` and a `_spec` suffix (clean shape), or has the relevant linter suppressed.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

-- Minimal dummy function for testing.
private def dummyFn2 (n : Nat) : Result Nat := .ok n

/-! ## `linter.curve25519.specSourceDoc` — `@[step]` theorem in a module with no `Source:` line -/

-- /--
-- warning: This file contains an `@[step]` theorem but the module docstring does not include a `Source:` line. Add e.g.:
-- /-! ...
-- Source: path/to/rust/file.rs
-- -/

-- Note: This linter can be disabled with `set_option linter.curve25519.specSourceDoc false`
-- -/
-- #guard_msgs in
-- Triggers `specSourceDoc`: the module doc above has no `Source:` line.
@[step]
theorem dummyFn2_spec (n : Nat) : dummyFn2 n ⦃ r => r = n ⦄ := by simp [dummyFn2]

/-! ### Suppressing `specSourceDoc` -/

-- No warning expected: `specSourceDoc` is suppressed.
#guard_msgs in
set_option linter.curve25519.specSourceDoc false in
@[step]
theorem dummyFn2_suppressed_spec (n : Nat) : dummyFn2 n ⦃ r => r = n ⦄ := by simp [dummyFn2]

/-! ### `specStep` still fires independently when `@[step]` is absent -/

/--
warning: Spec theorem `dummyFn2_plain_spec` is missing the `@[step]` attribute. Add `@[step]` before `theorem` so the Aeneas `step` tactic can find this spec.

Note: This linter can be disabled with `set_option linter.curve25519.specStep false`
-/
#guard_msgs in
-- No `@[step]` → `specSourceDoc` does NOT fire (only `specStep` fires).
theorem dummyFn2_plain_spec (n : Nat) : dummyFn2 n ⦃ r => r = n ⦄ := by simp [dummyFn2]
