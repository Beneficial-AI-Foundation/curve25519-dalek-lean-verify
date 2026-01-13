/-
  Types: Unified data structures for function analysis.

  This module defines the core `FunctionRecord` type that represents
  a function extracted from Rust code, along with its metadata,
  dependencies, and verification status.
-/
import Lean
import Lean.Data.Json

open Lean

namespace Utils.Lib.Types

/-- Information parsed from a function's Aeneas-generated docstring.
    Format: `/-- [rust_name]: Source: 'path', lines X:Y-A:B -/` -/
structure DocstringInfo where
  rustName : Option String := none
  source : Option String := none
  lineStart : Option Nat := none
  lineEnd : Option Nat := none
  deriving Repr, Inhabited

/-- A complete record of a function and its analysis results. -/
structure FunctionRecord where
  /-- Fully-qualified Lean name (e.g., `curve25519_dalek.backend.serial...`) -/
  leanName : Name
  /-- Original Rust function path from docstring (e.g., `curve25519_dalek::backend::serial...`) -/
  rustName : Option String := none
  /-- Source file path from docstring -/
  source : Option String := none
  /-- Line range (start, end) from docstring -/
  lineRange : Option (Nat × Nat) := none
  /-- Direct dependencies filtered to relevant functions only -/
  dependencies : Array Name := #[]
  /-- Nested child functions (functions whose name has this as a prefix) -/
  nestedChildren : Array Name := #[]
  /-- True if source is from the target crate (not /rustc/, /cargo/registry/, etc.) -/
  isRelevant : Bool := false
  /-- True if this is an Aeneas extraction artifact (_body, _loop, etc.) -/
  isExtractionArtifact : Bool := false
  /-- True if this function is explicitly hidden via Config.hiddenFunctions -/
  isHidden : Bool := false
  /-- True if a `{leanName}_spec` theorem exists -/
  isSpecified : Bool := false
  /-- True if specified AND the spec proof contains no `sorry` -/
  isVerified : Bool := false
  /-- True if verified AND all transitive dependencies are verified -/
  isFullyVerified : Bool := false
  /-- File path where the spec theorem is defined (e.g., "Curve25519Dalek/Specs/.../Add.lean") -/
  specFilePath : Option String := none
  /-- The spec theorem docstring, if one exists -/
  specDocstring : Option String := none
  /-- The spec theorem statement (without proof), if one exists -/
  specStatement : Option String := none
  deriving Repr, Inhabited

/-!
## JSON Serialization

Output format for external tools and status tracking.
-/

/-- JSON output structure for a single function -/
structure FunctionOutput where
  lean_name : String
  rust_name : Option String := none
  source : Option String := none
  lines : Option String := none
  dependencies : Array String := #[]
  nested_children : Array String := #[]
  is_relevant : Bool := false
  is_extraction_artifact : Bool := false
  is_hidden : Bool := false
  specified : Bool := false
  verified : Bool := false
  fully_verified : Bool := false
  spec_file : Option String := none
  spec_docstring : Option String := none
  spec_statement : Option String := none
  deriving ToJson, FromJson, Repr

/-- Convert a FunctionRecord to JSON-serializable output -/
def FunctionRecord.toOutput (rec : FunctionRecord) : FunctionOutput :=
  let lines := match rec.lineRange with
    | some (s, e) => some s!"L{s}-L{e}"
    | none => none
  { lean_name := rec.leanName.toString
    rust_name := rec.rustName
    source := rec.source
    lines := lines
    dependencies := rec.dependencies.map (·.toString)
    nested_children := rec.nestedChildren.map (·.toString)
    is_relevant := rec.isRelevant
    is_extraction_artifact := rec.isExtractionArtifact
    is_hidden := rec.isHidden
    specified := rec.isSpecified
    verified := rec.isVerified
    fully_verified := rec.isFullyVerified
    spec_file := rec.specFilePath
    spec_docstring := rec.specDocstring
    spec_statement := rec.specStatement }

/-- Output structure for list of functions -/
structure FunctionListOutput where
  functions : Array FunctionOutput
  deriving ToJson, FromJson, Repr

/-- Render function list output to pretty JSON -/
def renderFunctionListOutput (output : FunctionListOutput) : String :=
  (toJson output).pretty

/-!
## Input Structures

For reading function lists from JSON files (e.g., for deps analysis).
-/

/-- Input: A single function to analyze -/
structure FunctionInput where
  lean_name : String
  deriving FromJson, ToJson, Repr

/-- Input: List of functions to analyze -/
structure FunctionListInput where
  functions : Array FunctionInput
  deriving FromJson, ToJson, Repr

/-- Parse JSON input from string -/
def parseInput (s : String) : Except String FunctionListInput :=
  match Json.parse s with
  | .error e => .error s!"JSON parse error: {e}"
  | .ok json =>
    match fromJson? json with
    | .error e => .error s!"JSON decode error: {e}"
    | .ok input => .ok input

end Utils.Lib.Types
