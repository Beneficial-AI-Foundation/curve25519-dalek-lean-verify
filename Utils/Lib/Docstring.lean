/-
  Docstring: Parsing utilities for Aeneas-generated docstrings.

  Aeneas generates docstrings with Rust function info, source file, and line numbers.
  This module provides functions to extract structured information from these docstrings.
-/
import Lean
import Utils.Lib.Types

open Lean

namespace Utils.Lib.Docstring

open Utils.Lib.Types

/-- Extract the Rust function name from between `[` and `]` in the docstring. -/
def extractRustName (doc : String) : Option String :=
  -- Find first '[' and matching ']'
  let parts := doc.splitOn "["
  if h : parts.length >= 2 then
    let afterBracket := parts[1]
    let endParts := afterBracket.splitOn "]"
    if h2 : endParts.length >= 1 then
      let content := endParts[0].trim
      -- Remove trailing ':' if present
      some (if content.endsWith ":" then content.dropRight 1 else content)
    else none
  else none

/-- Extract the source file path from `Source: 'path'` pattern. -/
def extractSourceFile (doc : String) : Option String :=
  let pattern := "Source: '"
  let parts := doc.splitOn pattern
  if h : parts.length >= 2 then
    let afterPattern := parts[1]
    -- Find closing quote
    let quoteParts := afterPattern.splitOn "'"
    if h2 : quoteParts.length >= 1 then
      some quoteParts[0]
    else none
  else none

/-- Parse line range from `lines X:Y-A:B` pattern. Returns (startLine, endLine). -/
def extractLineRange (doc : String) : Option (Nat × Nat) :=
  let pattern := "lines "
  let parts := doc.splitOn pattern
  if h : parts.length >= 2 then
    let afterPattern := parts[1]
    -- Split on '-' to get start and end parts
    match afterPattern.splitOn "-" with
    | [startPart, endPart] =>
      -- Extract just the line number (before any ':' for column info)
      let startLine := (startPart.takeWhile Char.isDigit).toNat?
      let endLine := (endPart.takeWhile Char.isDigit).toNat?
      match startLine, endLine with
      | some st, some en => some (st, en)
      | _, _ => none
    | _ => none
  else none

/-- Parse a complete docstring into structured info -/
def parseDocstring (doc : String) : DocstringInfo :=
  { rustName := extractRustName doc
    source := extractSourceFile doc
    lineStart := (extractLineRange doc).map Prod.fst
    lineEnd := (extractLineRange doc).map Prod.snd }

/-- Get docstring for a constant from the environment -/
def getDocstring (env : Environment) (name : Name) : IO (Option String) :=
  Lean.findDocString? env name

/-- Get parsed docstring info for a constant -/
def getDocstringInfo (env : Environment) (name : Name) : IO DocstringInfo := do
  match ← getDocstring env name with
  | some doc => return parseDocstring doc
  | none => return default

end Utils.Lib.Docstring
