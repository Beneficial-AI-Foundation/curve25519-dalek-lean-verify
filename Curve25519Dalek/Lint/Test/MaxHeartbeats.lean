/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang-Liao
-/
import Curve25519Dalek.Lint.Basic

/-!
# Tests for `linter.curve25519.maxHeartbeatsMultiple`

Verifies that `set_option maxHeartbeats N in` (and `synthInstance.maxHeartbeats`) triggers a
warning when `N` is not zero and not a multiple of 200000, and is silent otherwise.

No `@[step]` attributes are used here, so the three spec-style linters are all silent.
Theorem names do not end with `_spec` to avoid `specStep` warnings.
-/

/-! ## Bad values — not a multiple of 200000 -/

/--
warning: `maxHeartbeats` value 100000 is not a multiple of 200000. Use a standard increment (e.g. 200000, 400000, 800000).

Note: This linter can be disabled with `set_option linter.curve25519.maxHeartbeatsMultiple false`
-/
#guard_msgs in
-- 100000 is not a multiple of 200000.
set_option maxHeartbeats 100000 in
theorem hb_bad_one : True := trivial

/--
warning: `maxHeartbeats` value 300000 is not a multiple of 200000. Use a standard increment (e.g. 200000, 400000, 800000).

Note: This linter can be disabled with `set_option linter.curve25519.maxHeartbeatsMultiple false`
-/
#guard_msgs in
-- 300000 is not a multiple of 200000.
set_option maxHeartbeats 300000 in
theorem hb_bad_two : True := trivial

/--
warning: `maxHeartbeats` value 300000 is not a multiple of 200000. Use a standard increment (e.g. 200000, 400000, 800000).

Note: This linter can be disabled with `set_option linter.curve25519.maxHeartbeatsMultiple false`
-/
#guard_msgs in
-- `synthInstance.maxHeartbeats` is also checked (its name contains `maxHeartbeats`).
set_option synthInstance.maxHeartbeats 300000 in
theorem hb_synth_bad : True := trivial

/-! ## Good values — multiples of 200000 or zero -/

-- No warning: 400000 is a multiple of 200000.
#guard_msgs in
set_option maxHeartbeats 400000 in
theorem hb_good_one : True := trivial

-- No warning: 800000 is a multiple of 200000.
#guard_msgs in
set_option maxHeartbeats 800000 in
theorem hb_good_two : True := trivial

-- No warning: 0 is the special "disabled" value.
#guard_msgs in
set_option maxHeartbeats 0 in
theorem hb_zero : True := trivial

/-! ## Suppression -/

-- No warning: linter is suppressed.
#guard_msgs in
set_option linter.curve25519.maxHeartbeatsMultiple false in
set_option maxHeartbeats 100000 in
theorem hb_suppressed : True := trivial
