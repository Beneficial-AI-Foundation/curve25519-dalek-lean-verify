/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang-Liao
-/
import Aeneas
import Curve25519Dalek.Lint.Basic

/-!
# Tests for `linter.curve25519.specStep` and `linter.curve25519.specSuffix`

Tests for the two name-convention linters.  This module-level docstring includes a `Source:`
line so that `linter.curve25519.specSourceDoc` does **not** fire here, keeping each
`#guard_msgs` block focused on exactly one linter at a time.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

-- Minimal dummy function: returns its argument wrapped in `ok`.
-- The theorems below use this so that `@[step]` can be applied without errors
-- (the attribute requires a `spec (f …) P` shape).
private def dummyFn (n : Nat) : Result Nat := .ok n

/-! ## `linter.curve25519.specStep` — `*_spec` theorem missing `@[step]` -/

/--
warning: Spec theorem `dummyFn_spec` is missing the `@[step]` attribute. Add `@[step]` before `theorem` so the Aeneas `step` tactic can find this spec.

Note: This linter can be disabled with `set_option linter.curve25519.specStep false`
-/
#guard_msgs in
-- Triggers `specStep`: name ends with `_spec` but `@[step]` is absent.
theorem dummyFn_spec (n : Nat) : dummyFn n ⦃ r => r = n ⦄ := by simp [dummyFn]

-- No warning expected: `specStep` is suppressed.
#guard_msgs in
set_option linter.curve25519.specStep false in
theorem dummyFn_suppressed_spec (n : Nat) : dummyFn n ⦃ r => r = n ⦄ := by simp [dummyFn]

/-! ## `linter.curve25519.specSuffix` — `@[step]` theorem without `_spec` suffix -/

/--
warning: Theorem `dummyFn_bad_name` carries `@[step]` but its name does not end with `_spec`. Rename it to `dummyFn_bad_name_spec` (or adjust to the full function path with `_spec` suffix).

Note: This linter can be disabled with `set_option linter.curve25519.specSuffix false`
-/
#guard_msgs in
-- Triggers `specSuffix`: has `@[step]` but the name has no `_spec` suffix.
@[step]
theorem dummyFn_bad_name (n : Nat) : dummyFn n ⦃ r => r = n ⦄ := by simp [dummyFn]

-- No warning expected: `specSuffix` is suppressed.
#guard_msgs in
set_option linter.curve25519.specSuffix false in
@[step]
theorem dummyFn_suppressed_name (n : Nat) : dummyFn n ⦃ r => r = n ⦄ := by simp [dummyFn]

/-! ## Clean case — both `@[step]` and `_spec` present, no warnings -/

-- No warning expected from any of the three spec-style linters.
#guard_msgs in
@[step]
theorem dummyFn_clean_spec (n : Nat) : dummyFn n ⦃ r => r = n ⦄ := by simp [dummyFn]
