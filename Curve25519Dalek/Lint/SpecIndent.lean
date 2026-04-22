/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Lean
import Mathlib.Tactic.Linter

/-!
# Linter: `specIndent` — spec theorem indentation style

Enforces the four indentation rules for `@[step]` spec theorems defined in `doc/STYLE_GUIDE.md`:

| Location | Expected column (0-indexed) |
|---|---|
| Continuation line on a new line after the `theorem` line (arguments, preconditions, function application) | 4 |
| Postcondition body on a new line after `=>` in the WP binder | 6 |
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

/-- 1-indexed source line of `stx`'s trailing (end) position. -/
private def tailLineOf (stx : Syntax) (fm : FileMap) : Option Nat :=
  stx.getTailPos? >>= fun p => some (fm.toPosition p).line

/-- `true` iff `stx` is a `A ∧ B` node (the `«term_∧_»` notation).
Matches by checking that the node has exactly three children and the middle child is the
`∧` atom.  We use the atom-value check rather than `stx.getKind == \`«term_∧_»` to stay
independent of namespace resolution details. -/
private def isAndNode (stx : Syntax) : Bool :=
  stx.getArgs.size == 3 &&
  match stx.getArgs[1]? with
  | some (Syntax.atom _ v) => v.trimAscii == "∧"
  | _                      => false

/-- Recursively collect every WP-binder body — the term immediately after `=>` in
`⦃ binder => body ⦄` — that starts on a new line after `=>` and is NOT at `expected` column. -/
private partial def collectMisindentedWpBodies
    (stx : Syntax) (fm : FileMap) (expected : Nat) : Array Syntax :=
  let childResults := stx.getArgs.flatMap (collectMisindentedWpBodies · fm expected)
  let args := stx.getArgs
  -- Only match nodes that have ` ⦃ ` as a direct atom child (WP binder notation).
  let hasLLBracket := args.any fun c =>
    match c with | Syntax.atom _ v => v.trimAscii == "⦃" | _ => false
  if !hasLLBracket then childResults
  else
    match args.findIdx? (fun c => match c with | Syntax.atom _ v => v.trimAscii == "=>" | _ => false) with
    | none => childResults
    | some arrowIdx =>
      match args[arrowIdx]?, args[arrowIdx + 1]? with
      | some arrowAtom, some body =>
        match lineOf arrowAtom fm, lineOf body fm, colOf body fm with
        | some arrowLine, some bodyLine, some bodyCol =>
          if bodyLine > arrowLine && bodyCol ≠ expected then childResults.push body
          else childResults
        | _, _, _ => childResults
      | _, _ => childResults

/-- Recursively collect every WP-binder body term (the `body` in `⦃ binder => body ⦄`).
Used to scope `∧`-RHS checks to postconditions only. -/
private partial def collectWpBodies (stx : Syntax) : Array Syntax :=
  let args := stx.getArgs
  let hasLLBracket := args.any fun c =>
    match c with | Syntax.atom _ v => v.trimAscii == "⦃" | _ => false
  if !hasLLBracket then args.flatMap collectWpBodies
  else
    match args.findIdx? (fun c => match c with | Syntax.atom _ v => v.trimAscii == "=>" | _ => false) with
    | none     => #[]
    | some idx => match args[idx + 1]? with
      | some body => #[body]
      | none      => #[]


private partial def collectMisindentedAndRhs_aux
    (stx : Syntax) (fm : FileMap) (expected : Nat) : Array (Syntax × String) :=
  if isAndNode stx then
    match stx.getArgs[0]?, stx.getArgs[1]?, stx.getArgs[2]? with
    | some lhs, some andNode, some rhs =>
        let acc := collectMisindentedAndRhs_aux rhs fm expected
        match tailLineOf lhs fm, lineOf andNode fm, lineOf rhs fm, colOf rhs fm with
        | some lhsTailLine, some andLine, some rhsLine, some rhsCol =>
          let acc :=
            if andLine > lhsTailLine then
              acc.push (andNode,
                "∧ operator should be appended to the end of the preceding line, \
                not placed at the start of a new line, \
                per the spec theorem style guide.")
            else acc
          let acc :=
            if rhsLine > andLine && rhsCol ≠ expected then
              acc.push (rhs,
                s!"Postcondition conjunct is at column {rhsCol}, expected {expected}. \
                Conjunction operands on new lines should be indented {expected} spaces \
                per the spec theorem style guide.")
            else acc
          acc
        | _, _, _, _ => acc
    | _, _, _ => #[]
  else #[]


private partial def collectMisindentedAndRhs
    (stx : Syntax) (fm : FileMap) (expected : Nat) : Array (Syntax × String) :=
  if isAndNode stx then
    collectMisindentedAndRhs_aux stx fm expected
  else
    stx.getArgs.flatMap (collectMisindentedAndRhs · fm expected)


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
  let some typeTerm  := typeSpec.getArgs[1]? | return

  -- ── Check 1: Continuation lines at column 4 ─────────────────────────────
  -- Arguments, preconditions, and the function application line all share the
  -- same 4-space rule.  Keep only the first node on each continuation line so
  -- that multiple binders sharing a line (e.g. `(n : Nat) (_h : n > 0)`) count
  -- as one logical line.
  let (firstPerLine, _) := (bindersNode.getArgs ++ #[typeTerm]).foldl
    (fun acc node =>
      let (arr, seen) := acc
      match lineOf node fm with
      | some l => if l > kwLine && !seen.contains l then (arr.push node, seen.cons l)
                  else acc
      | none   => acc)
    ((#[] : Array Syntax), ([] : List Nat))
  for node in firstPerLine do
    if let some nodeCol := colOf node fm then
      unless nodeCol == 4 do
        logLint linter.curve25519.specIndent node
          m!"Continuation line is at column {nodeCol}, expected 4. \
            Arguments, preconditions, and the function application line \
            on a new line should be indented 4 spaces \
            per the spec theorem style guide."

  -- ── Check 3a: First postcondition body at column 6 ──────────────────────
  for node in collectMisindentedWpBodies typeTerm fm 6 do
    let col := (colOf node fm).getD 0
    logLint linter.curve25519.specIndent node
      m!"Postcondition body is at column {col}, expected 6. \
        The postcondition body after `=>` should be indented 6 spaces \
        per the spec theorem style guide."

  -- ── Check 3b: ∧ postcondition RHS at column 6 ────────────────────────────
  for body in collectWpBodies typeTerm do
    for (node, msg) in collectMisindentedAndRhs body fm 6 do
      logLint linter.curve25519.specIndent node m!"{msg}"

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
