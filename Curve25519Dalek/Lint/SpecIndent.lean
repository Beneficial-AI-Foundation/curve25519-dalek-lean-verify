/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhang-Liao
-/
import Lean

/-!
# Linter: `specIndent` — spec theorem indentation style

Enforces the four indentation rules for `@[step]` spec theorems defined in `doc/STYLE_GUIDE.md`:

| Location | Expected column (0-indexed) |
|---|---|
| Continuation binder on a new line after the `theorem` line | 4 |
| Function application / type after `:` (when on a new line) | 4 |
| `∧` RHS postcondition on a new line inside the WP binder | 6 |
| Proof body after `by` (when on a new line) | 2 |

All checks apply only to `@[step]` theorems.  The linter is controlled by a single option
`linter.curve25519.specIndent` so that a justified deviation can be suppressed uniformly.

Syntax-tree shapes assumed (Lean 4.26, confirmed from `Lean.Parser.Command`):
```
Lean.Parser.Command.declaration
  [0] declModifiers          ← @[step] lives here
  [1] Lean.Parser.Command.theorem
        [0] "theorem" keyword atom
        [1] Lean.Parser.Command.declId
        [2] Lean.Parser.Command.declSig
              [0] null-array of binders  (Term.binderIdent | Term.bracketedBinder)*
              [1] Lean.Parser.Term.typeSpec
                    [0] ":" atom
                    [1] type term
        [3] Lean.Parser.Command.declValSimple
              [0] ":=" atom
              [1] declBody (the proof term)
              [2] Termination.suffix
              [3] optional whereDecls
```
`byTactic` (kind `Lean.Parser.Term.byTactic`):
```
  [0] "by " atom
  [1] tacticSeq (position = first tactic's first token)
```
`«term_∧_»` node (from `infixr:35 " ∧ " => And`):
```
  [0] left operand
  [1] "∧" atom
  [2] right operand
```
-/

namespace Curve25519Dalek.Lint

open Lean Elab Command Linter

/-! ## Option -/

/-- Warns when a `@[step]` theorem's indentation deviates from the project spec style guide.
See `doc/STYLE_GUIDE.md` §"Indentation Structure". -/
register_option linter.curve25519.specIndent : Bool := {
  defValue := true
  descr := "Warns when a `@[step]` theorem's indentation deviates from the style guide."
}

/-! ## Helpers -/

/-- Return `true` when the declaration command `stx` carries an `@[step]` attribute.
Only inspects `declModifiers` (`stx[0]`) to avoid false positives from proof bodies. -/
private def hasStepAttr (stx : Syntax) : Bool :=
  match stx.getArgs[0]? with
  | none      => false
  | some mods => mods.find? (fun s => s.isIdent && s.getId == `step) |>.isSome

/-- 0-indexed column of `stx`'s leading source position. -/
private def colOf (stx : Syntax) (fm : FileMap) : Option Nat :=
  stx.getPos? >>= fun p => some (fm.toPosition p).column

/-- 1-indexed source line of `stx`'s leading position. -/
private def lineOf (stx : Syntax) (fm : FileMap) : Option Nat :=
  stx.getPos? >>= fun p => some (fm.toPosition p).line

/-- `true` iff `stx` is a `A ∧ B` node (the `«term_∧_»` notation).
Matches by checking that the node has exactly three children and the middle child is the
`∧` atom.  We use the atom-value check rather than `stx.getKind == \`«term_∧_»` to stay
independent of namespace resolution details. -/
private def isAndNode (stx : Syntax) : Bool :=
  stx.getArgs.size == 3 &&
  match stx.getArgs[1]? with
  | some (Syntax.atom _ v) => v == "∧"
  | _                      => false

/-- Recursively collect every `∧`-RHS node that (a) starts on a line strictly after the
corresponding `∧` node's start line and (b) is NOT at `expected` column.
Returns the offending RHS nodes for diagnostic reporting. -/
private partial def collectMisindentedAndRhs
    (stx : Syntax) (fm : FileMap) (expected : Nat) : Array Syntax :=
  let childResults := stx.getArgs.flatMap (collectMisindentedAndRhs · fm expected)
  if isAndNode stx then
    match stx.getArgs[2]?, lineOf stx fm with
    | some rhs, some andLine =>
      match lineOf rhs fm, colOf rhs fm with
      | some rhsLine, some rhsCol =>
        if rhsLine > andLine && rhsCol ≠ expected then childResults.push rhs
        else childResults
      | _, _ => childResults
    | _, _ => childResults
  else childResults

/-! ## Linter -/

/-- Implementation of `linter.curve25519.specIndent`. -/
def specIndentLinter : Linter where run stx := do
  unless getLinterValue linter.curve25519.specIndent (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  let some inner := stx.getArgs[1]? | return
  unless inner.isOfKind ``Lean.Parser.Command.theorem do return
  unless hasStepAttr stx do return

  let fm ← getFileMap

  -- ── Extract key sub-trees ─────────────────────────────────────────────────
  let some kwNode  := inner.getArgs[0]? | return   -- "theorem" keyword
  let some sig     := inner.getArgs[2]? | return   -- declSig
  let some declVal := inner.getArgs[3]? | return   -- declVal

  let some kwLine  := lineOf kwNode fm  | return

  -- declSig[0] = binder array,  declSig[1] = typeSpec
  let some bindersNode := sig.getArgs[0]? | return
  let some typeSpec    := sig.getArgs[1]? | return
  -- typeSpec[0] = ":" atom,  typeSpec[1] = type term
  let some colonNode := typeSpec.getArgs[0]? | return
  let some typeTerm  := typeSpec.getArgs[1]? | return

  -- ── Check 1: Continuation binders at column 4 ────────────────────────────
  for binder in bindersNode.getArgs do
    if let some bLine := lineOf binder fm then
      if bLine > kwLine then
        if let some bCol := colOf binder fm then
          unless bCol == 4 do
            logLint linter.curve25519.specIndent binder
              m!"Continuation binder is at column {bCol}, expected 4. \
                Binders that wrap to a new line should be indented 4 spaces \
                per the spec theorem style guide."

  -- ── Check 2: Type / function application at column 4 ─────────────────────
  if let some colonLine := lineOf colonNode fm then
    if let some typeLine := lineOf typeTerm fm then
      if typeLine > colonLine then
        if let some typeCol := colOf typeTerm fm then
          unless typeCol == 4 do
            logLint linter.curve25519.specIndent typeTerm
              m!"The function application / type after `:` is at column {typeCol}, expected 4. \
                The type should start on a new line indented 4 spaces \
                per the spec theorem style guide."

  -- ── Check 3: ∧ postcondition RHS at column 6 ─────────────────────────────
  for node in collectMisindentedAndRhs typeTerm fm 6 do
    let col := (colOf node fm).getD 0
    logLint linter.curve25519.specIndent node
      m!"Postcondition conjunct is at column {col}, expected 6. \
        Conjunction operands on new lines should be indented 6 spaces \
        per the spec theorem style guide."

  -- ── Check 4: Proof body at column 2 ──────────────────────────────────────
  unless declVal.isOfKind ``Lean.Parser.Command.declValSimple do return
  -- declValSimple[0]=":=", [1]=declBody, [2]=Termination.suffix, [3]=whereDecls
  let some proofTerm := declVal.getArgs[1]? | return
  unless proofTerm.isOfKind ``Lean.Parser.Term.byTactic do return
  -- byTactic[0]="by ", [1]=tacticSeq
  let some byKw      := proofTerm.getArgs[0]? | return
  let some tacticSeq := proofTerm.getArgs[1]? | return
  if let some byLine  := lineOf byKw fm then
    if let some tacLine := lineOf tacticSeq fm then
      if tacLine > byLine then
        if let some tacCol := colOf tacticSeq fm then
          unless tacCol == 2 do
            logLint linter.curve25519.specIndent tacticSeq
              m!"Proof body is at column {tacCol}, expected 2. \
                Tactics after `by` should be indented 2 spaces \
                per the spec theorem style guide."

initialize addLinter specIndentLinter

end Curve25519Dalek.Lint
