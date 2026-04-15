/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang-Liao
-/
import Lean

/-!
# Linters: spec theorem style conventions

Three complementary linters enforcing the project's spec theorem conventions
(see `doc/STYLE_GUIDE.md`).  None of these overlap with any Mathlib standard linter.

* `linter.curve25519.specStep` — every `theorem`/`lemma` whose name ends with `_spec`
  must carry the `@[step]` attribute so the Aeneas `step` tactic can find it.

* `linter.curve25519.specSuffix` — every `theorem`/`lemma` that carries `@[step]`
  must have a name ending with `_spec`.

* `linter.curve25519.specSourceDoc` — every module that contains at least one `@[step]`
  theorem must have a module-level docstring (`/-! ... -/`) that includes a `Source:` line
  giving the path to the original Rust source file.
-/

namespace Curve25519Dalek.Lint

open Lean Elab Command Linter

/-! ## Linter options -/

/-- Warns when a theorem/lemma whose name ends with `_spec` is missing the `@[step]`
attribute required by the style guide. -/
register_option linter.curve25519.specStep : Bool := {
  defValue := true
  descr := "Warns when a `*_spec` theorem is missing the `@[step]` attribute."
}

/-- Warns when a theorem/lemma carrying `@[step]` does not have a name ending with `_spec`. -/
register_option linter.curve25519.specSuffix : Bool := {
  defValue := true
  descr := "Warns when an `@[step]` theorem is not named `*_spec`."
}

/-- Warns when a module that contains at least one `@[step]` theorem lacks a module-level
docstring with a `Source:` line identifying the Rust source file. -/
register_option linter.curve25519.specSourceDoc : Bool := {
  defValue := true
  descr := "Warns when a spec file with `@[step]` theorems has no `Source:` in its module doc."
}

/-! ## Helpers -/

/-- Given a `Lean.Parser.Command.declaration` syntax node (the outer command that linters
receive), return the ident syntax node for the declared name, or `none` if the structure is
unexpected or if the inner declaration is not a `theorem`/`lemma`.

Lean 4 command layout (kind `Lean.Parser.Command.declaration`):
```
[0] declModifiers   [1] innerDecl
```
When `innerDecl` is a theorem/lemma (kind `Lean.Parser.Command.theorem`):
```
[0] "theorem"/"lemma" keyword   [1] declId   [2] declSig   [3] declVal
```
`declId` layout: `[0]` ident (name)  `[1]` optional universe declaration.

So the name ident is at `stx[1][1][0]`. -/
private def getTheoremIdent (stx : Syntax) : Option Syntax :=
  stx.getArgs[1]? >>= (·.getArgs[1]?) >>= (·.getArgs[0]?)

/-- Return `true` when the declaration command `stx` carries an `@[step]` attribute.

We search only within `declModifiers` (`stx.getArgs[0]`, the first child of the outer
`Lean.Parser.Command.declaration` node) to avoid false positives from identifiers named
`step` appearing elsewhere in the proof body.
The `@[step]` attribute is represented as an unqualified ident with value `step` inside
the attribute list, which lives exclusively in `declModifiers`. -/
private def hasStepAttr (stx : Syntax) : Bool :=
  match stx.getArgs[0]? with
  | none => false
  | some mods => mods.find? (fun s => s.isIdent && s.getId == `step) |>.isSome

/-! ## Combined linter -/

/-- Implementation of the three spec-theorem style linters. -/
def specStyleLinter : Linter where run stx := do
  -- The outer command node has kind `Lean.Parser.Command.declaration`.
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  -- The inner declaration must be a theorem/lemma (not def, class, etc.).
  let some inner := stx.getArgs[1]? | return
  unless inner.isOfKind ``Lean.Parser.Command.theorem do return
  -- Extract the declared name; skip if the syntax is unexpectedly shaped.
  let some nameIdent := getTheoremIdent stx | return
  let name     := nameIdent.getId.toString
  let endsSpec := name.endsWith "_spec"
  let hasStep  := hasStepAttr stx
  -- 1. specStep: *_spec theorem missing @[step]
  if getLinterValue linter.curve25519.specStep (← getLinterOptions) then
    if endsSpec && !hasStep then
      logLint linter.curve25519.specStep nameIdent
        m!"Spec theorem `{name}` is missing the `@[step]` attribute. \
          Add `@[step]` before `theorem` so the Aeneas `step` tactic can find this spec."
  -- 2. specSuffix: @[step] theorem without _spec suffix
  if getLinterValue linter.curve25519.specSuffix (← getLinterOptions) then
    if hasStep && !endsSpec then
      logLint linter.curve25519.specSuffix nameIdent
        m!"Theorem `{name}` carries `@[step]` but its name does not end with `_spec`. \
          Rename it to `{name}_spec` (or adjust to the full function path with `_spec` suffix)."
  -- 3. specSourceDoc: @[step] theorem in a module without a Source: line
  if getLinterValue linter.curve25519.specSourceDoc (← getLinterOptions) then
    if hasStep then
      let docs := Lean.getMainModuleDoc (← getEnv)
      -- Check for a line that actually starts with "Source: " (space after colon).
      -- Plain `contains "Source:"` would falsely match imported module docs that
      -- mention the string inside prose or table cells (e.g. "`Source:`").
      unless docs.any (fun d =>
          d.doc.splitOn "\n" |>.any (fun line =>
            (line.dropWhile Char.isWhitespace).startsWith "Source:")) do
        logLint linter.curve25519.specSourceDoc stx
          m!"This file contains an `@[step]` theorem but the module docstring \
            does not include a `Source:` line. Add e.g.:\n\
            /-! ...\n\
            Source: path/to/rust/file.rs\n\
            -/"

initialize addLinter specStyleLinter

end Curve25519Dalek.Lint
