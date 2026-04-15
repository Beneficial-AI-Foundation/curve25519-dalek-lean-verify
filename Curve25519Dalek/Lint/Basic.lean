/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang-Liao
-/
import Curve25519Dalek.Lint.MaxHeartbeats
import Curve25519Dalek.Lint.SpecStyle
import Curve25519Dalek.Lint.SpecIndent

/-!
# Curve25519Dalek project linters

Importing this module activates all project-specific linters.  It is imported transitively
by `Curve25519Dalek.Aux` and `Curve25519Dalek.FunsExternal`, which together cover the full
transitive import graph of spec theorem files.

## Linters provided

| Option | What it checks |
|---|---|
| `linter.curve25519.maxHeartbeatsMultiple` | `set_option maxHeartbeats N in` with `N` not a multiple of 200000 |
| `linter.curve25519.specStep` | `*_spec` theorem missing `@[step]` |
| `linter.curve25519.specSuffix` | `@[step]` theorem not named `*_spec` |
| `linter.curve25519.specSourceDoc` | Spec file without `Source:` in module docstring |
| `linter.curve25519.specIndent` | `@[step]` theorem with wrong indentation (binders/type/postconditions/proof) |

All linters are enabled by default (`defValue := true`) and can be suppressed locally with a
documented `set_option linter.curve25519.* false in` — consistent with the style guide's
requirement that suppressions carry an explanatory comment.
-/
