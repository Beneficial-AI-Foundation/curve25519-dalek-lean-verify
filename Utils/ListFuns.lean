/-
  ListFuns: Core logic for listing functions defined in Curve25519Dalek/Funs.lean.

  This module provides reusable functions for extracting function definitions
  from the compiled Lean environment. The main entry point is `getFunsDefinitions`.

  CLI Usage:
    lake exe listfuns [output.json]

  Output JSON format:
    {
      "functions": [
        { "lean_name": "curve25519_dalek.some.function" },
        ...
      ]
    }

  If no output file is specified, prints to stdout.
-/
import Lean
import Lean.Data.Json
import Batteries.Data.String.Matcher

open Lean

namespace Utils.ListFuns

/-!
## Configuration

The following settings control which functions are included in the output.
Modify these to customize the filtering behavior.
-/

/-- The module name for Funs.lean -/
def funsModule : Name := `Curve25519Dalek.Funs

/-!
### Namespace Prefix Filters

Functions whose name (after `curve25519_dalek.`) starts with any of these
prefixes will be EXCLUDED from the output.

Examples of excluded names:
- `curve25519_dalek.core.ops.arith...` (prefix: `core`)
- `curve25519_dalek.subtle.Choice...` (prefix: `subtle`)
-/
def excludedNamespacePrefixes : List String := [
  "curve25519_dalek.core",     -- Rust core library implementations
  "curve25519_dalek.subtle",   -- Subtle crate implementations
  "_private"  --
]

/-!
### Suffix Filters

Functions whose name ends with any of these suffixes (CASE-SENSITIVE)
will be EXCLUDED from the output.

Examples of excluded names:
- `curve25519_dalek...EDWARDS_D_body` (suffix: `_body`)
- `curve25519_dalek...add_assign_loop` (suffix: `_loop`)
-/
def excludedSuffixes : List String := [
  "_body",             -- Internal body definitions for lazy constants (lowercase)
  "_loop",             -- Loop helper functions
  "_loop._unsafe_rec", -- Loop helper functions
  "_loop.mutual"       -- Loop helper functions
]

/-!
### Internal Name Patterns

Functions containing any of these patterns will be EXCLUDED.
-/
def excludedPatterns : List String := [
]

/-!
### Nested Function Filter

When enabled, functions that are "children" of other functions will be excluded.
A function B is a child of function A if B's name is A's name plus additional
components.

Example:
- `curve25519_dalek...Mul.mul` is kept (it's a top-level function)
- `curve25519_dalek...Mul.mul.LOW_51_BIT_MASK` is excluded (it's internal to `mul`)
-/
def filterNestedFunctions : Bool := true

/-!
## Implementation
-/

/-- Check if a ConstantInfo represents a definition (not a theorem, axiom, etc.) -/
def isDefinition (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false

/-- Check if a name starts with an excluded namespace prefix -/
def hasExcludedPrefix (name : Name) : Bool :=
  excludedNamespacePrefixes.any fun pfx =>
    pfx.toName.isPrefixOf name

/-- Check if string `s` ends with suffix `sfx` -/
def String.endsWith (s sfx : String) : Bool :=
  s.length >= sfx.length && s.drop (s.length - sfx.length) == sfx

/-- Check if a name ends with an excluded suffix (case-sensitive) -/
def hasExcludedSuffix (name : Name) : Bool :=
  let str := name.toString
  excludedSuffixes.any fun sfx =>
    str.endsWith sfx

/-- Check if a name contains an excluded pattern -/
def hasExcludedPattern (name : Name) : Bool :=
  let str := name.toString
  excludedPatterns.any fun pattern =>
    str.containsSubstr pattern

/-- Check if name B is a nested child of name A (A is a proper prefix of B) -/
def isNestedChild (parent child : Name) : Bool :=
  parent.isPrefixOf child && parent != child

/-- Filter out nested functions (functions that are children of other functions in the list) -/
def filterNested (names : Array Name) : Array Name :=
  if !filterNestedFunctions then names
  else
    -- A name is kept if no other name in the list is its proper prefix
    names.filter fun name =>
      !names.any fun other => isNestedChild other name

/-- Check if a name should be included based on all filter criteria -/
def shouldInclude (name : Name) : Bool :=
  !hasExcludedPrefix name &&
  !hasExcludedSuffix name &&
  !hasExcludedPattern name

/-- Get all function names defined in Funs.lean -/
def getFunsDefinitions (env : Environment) : IO (Array Name) := do
  -- Get the module index for Funs.lean
  let some moduleIdx := env.header.moduleNames.idxOf? funsModule
    | return #[]  -- Module not found

  -- Get constant names directly from the module data
  let constNames := env.header.moduleData[moduleIdx]!.constNames

  let mut candidates : Array Name := #[]
  for name in constNames do
    -- Look up the constant info
    if let some ci := env.find? name then
      -- Only include definitions (not theorems, axioms, etc.)
      if isDefinition ci && shouldInclude name then
        candidates := candidates.push name

  -- Filter out nested functions
  let filtered := filterNested candidates

  -- Sort alphabetically for consistent output
  return filtered.qsort (·.toString < ·.toString)

/-- Load the Curve25519Dalek environment -/
def loadEnvironment : IO Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  importModules #[{ module := `Curve25519Dalek }] {}

/-- Get all function names as strings (convenience function for other scripts) -/
def getFunsDefinitionsAsStrings (env : Environment) : IO (Array String) := do
  let names ← getFunsDefinitions env
  return names.map (·.toString)

/-- Output structure for a single function -/
structure FunctionOutput where
  lean_name : String
  deriving ToJson, FromJson, Repr

/-- Output structure for the full list -/
structure ListOutput where
  functions : Array FunctionOutput
  deriving ToJson, FromJson, Repr

/-- Render output to JSON string -/
def renderOutput (output : ListOutput) : String :=
  (toJson output).pretty

end Utils.ListFuns

open Utils.ListFuns

/-- Print usage information -/
def printUsage : IO Unit := do
  IO.println "Usage: lake exe listfuns [output.json]"
  IO.println ""
  IO.println "Lists all functions defined in Curve25519Dalek/Funs.lean."
  IO.println ""
  IO.println "Arguments:"
  IO.println "  [output.json]  Output file (prints to stdout if omitted)"
  IO.println ""
  IO.println "Output format:"
  IO.println "  { \"functions\": [{ \"lean_name\": \"curve25519_dalek.some.function\" }, ...] }"

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  let outputPath : Option String := args.head?

  -- Load environment
  IO.eprintln "Loading Curve25519Dalek module..."
  let env ← loadEnvironment
  IO.eprintln "Module loaded successfully"

  -- Get all functions from Funs.lean
  let names ← getFunsDefinitions env
  IO.eprintln s!"Found {names.size} definitions in {funsModule}"

  -- Build output
  let functions := names.map fun name => { lean_name := name.toString : FunctionOutput }
  let output : ListOutput := { functions }

  -- Write or print output
  let jsonOutput := renderOutput output
  match outputPath with
  | some path =>
    IO.FS.writeFile path jsonOutput
    IO.println s!"Results written to {path}"
  | none =>
    IO.println jsonOutput

  return 0
