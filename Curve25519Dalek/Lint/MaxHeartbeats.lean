/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang-Liao
-/
import Lean

/-!
# Linter: `maxHeartbeats` values must be multiples of 200000

Checks that `set_option maxHeartbeats N in ...` (including `synthInstance.maxHeartbeats`)
uses `N = 0` (disabled) or `N` divisible by 200000.  Standard increments are 200000, 400000,
800000, etc.

This linter is **complementary** to `linter.style.maxHeartbeats`, which enforces an explanatory
comment.  That linter ensures the *comment* is present; this linter enforces the *granularity*
of the value.  Neither check is subsumed by the other.
-/

namespace Curve25519Dalek.Lint

open Lean Elab Command Linter

/-- Warns on `set_option maxHeartbeats N in ...` (or `synthInstance.maxHeartbeats`) where
`N ≠ 0` and `N % 200000 ≠ 0`.  The style guide mandates using multiples of 200000 as
standard increments (e.g. 200000, 400000, 800000). -/
register_option linter.curve25519.maxHeartbeatsMultiple : Bool := {
  defValue := true
  descr := "Warns on `set_option maxHeartbeats N in ...` where N is not a multiple of 200000."
}

/-- Walk `stx` recursively and accumulate every `set_option <opt> N in <body>` node
where `<opt>` contains the component `maxHeartbeats`, `N ≠ 0`, and `N % 200000 ≠ 0`. -/
private partial def collectBadHeartbeats : Syntax → Array (Syntax × Nat)
  | stx@`(command| set_option $opt $n:num in $_) =>
    -- Recurse into children first (catches nested set_option blocks).
    let inner := stx.getArgs.flatMap collectBadHeartbeats
    if opt.getId.components.contains `maxHeartbeats then
      let val := n.getNat
      if val != 0 && val % 200000 != 0 then inner.push (stx, val) else inner
    else
      inner
  | stx@`(command| set_option $opt $_ in $_) =>
    -- Stop recursing when entering a scope that suppresses this linter.
    -- The inner command runs with the linter disabled; reporting from the outer
    -- scope would bypass the user's explicit suppression.
    if opt.getId.toString == "linter.curve25519.maxHeartbeatsMultiple" then #[]
    else stx.getArgs.flatMap collectBadHeartbeats
  | stx => stx.getArgs.flatMap collectBadHeartbeats

/-- The `linter.curve25519.maxHeartbeatsMultiple` linter. -/
def maxHeartbeatsMultipleLinter : Linter where run stx := do
  unless getLinterValue linter.curve25519.maxHeartbeatsMultiple (← getLinterOptions) do return
  for (node, val) in collectBadHeartbeats stx do
    logLint linter.curve25519.maxHeartbeatsMultiple node
      m!"`maxHeartbeats` value {val} is not a multiple of 200000. \
        Use a standard increment (e.g. 200000, 400000, 800000)."

initialize addLinter maxHeartbeatsMultipleLinter

end Curve25519Dalek.Lint
