/-
  Deps: A CLI tool to analyze Lean functions for verification status and dependencies.

  This tool loads a compiled Lean environment and analyzes functions to determine:
  1. Their dependencies on other functions in the input set
  2. Whether they have a specification theorem (`{function}_spec`)
  3. Whether that specification is fully proven (no `sorry`)
  4. Whether all transitive dependencies are also verified

  Usage:
    lake exe deps <input.json> [output.json]

  Input JSON format:
    {
      "functions": [
        { "lean_name": "curve25519_dalek.some.function" },
        ...
      ]
    }

  Output JSON format:
    {
      "functions": [
        {
          "lean_name": "curve25519_dalek.some.function",
          "dependencies": ["dep1", "dep2", ...],
          "specified": true,
          "verified": true,
          "fully_verified": false
        },
        ...
      ]
    }

  Output fields:
  - lean_name: The fully-qualified Lean name of the function
  - dependencies: Other functions from the input set that this function depends on
  - specified: True if a theorem `{lean_name}_spec` exists in the environment
  - verified: True if specified AND the spec theorem's proof contains no `sorry`
  - fully_verified: True if verified AND all transitive dependencies are also verified

  Naming convention:
  - Functions must be specified with their exact fully-qualified Lean names
  - Spec theorems must be named `{function_name}_spec` in the same namespace

  Exits with code 1 on any error (missing function, parse error, etc.)

  Example:
    lake exe deps functions.json deps.json
-/
import Lean
import Std.Data.HashSet
import Utils.Json
import Utils.Analysis

open Lean
open Utils.Json
open Utils.Analysis

/-- Print usage information -/
def printUsage : IO Unit := do
  IO.println "Usage: lake exe deps <input.json> [output.json]"
  IO.println ""
  IO.println "Analyzes Lean functions for verification status and dependencies."
  IO.println ""
  IO.println "Arguments:"
  IO.println "  <input.json>   JSON file with functions to analyze"
  IO.println "  [output.json]  Output file (prints to stdout if omitted)"
  IO.println ""
  IO.println "Input format:"
  IO.println "  { \"functions\": [{ \"lean_name\": \"curve25519_dalek.some.function\" }, ...] }"
  IO.println ""
  IO.println "Output fields:"
  IO.println "  - specified: theorem {name}_spec exists"
  IO.println "  - verified: specified AND proof has no sorry"
  IO.println "  - fully_verified: verified AND all transitive deps verified"
  IO.println ""
  IO.println "Example:"
  IO.println "  lake exe deps functions.json deps.json"

/-- Run the analysis -/
def runAnalysis (inputPath : String) (outputPath : Option String) : IO UInt32 := do
  -- Read input JSON
  let content ← IO.FS.readFile inputPath

  -- Parse input
  let input ← match parseInput content with
    | .ok i => pure i
    | .error e =>
      IO.eprintln s!"Error: {e}"
      return 1

  IO.println s!"Found {input.functions.size} functions to analyze"

  -- Build set of known function names for filtering
  let knownNames : Std.HashSet Name := input.functions.foldl
    (fun set func => set.insert func.lean_name.toName) {}

  -- Initialize Lean search path
  Lean.initSearchPath (← Lean.findSysroot)

  -- Import the main module (includes Funs and all Specs)
  IO.println "Loading Curve25519Dalek module..."
  let env ← importModules #[{ module := `Curve25519Dalek }] {}
  IO.println "Module loaded successfully"

  -- Analyze each function
  let mut results : Array DependencyOutput := #[]

  for func in input.functions do
    let name := func.lean_name.toName
    let analysisResult := analyzeFunction env knownNames name

    match analysisResult.error with
    | some msg =>
      IO.eprintln s!"Error analyzing '{func.lean_name}': {msg}"
      return 1
    | none =>
      let output : DependencyOutput := {
        lean_name := func.lean_name
        dependencies := analysisResult.filteredDeps.map (·.toString)
        specified := analysisResult.specified
        verified := analysisResult.verified
        fully_verified := isFullyVerified env knownNames name
      }
      results := results.push output

  IO.println s!"Analysis complete: {results.size} functions analyzed"

  -- Build output
  let output : AnalysisOutput := {
    functions := results
  }

  -- Write or print output
  let jsonOutput := renderOutput output
  match outputPath with
  | some path =>
    IO.FS.writeFile path jsonOutput
    IO.println s!"Results written to {path}"
  | none =>
    IO.println jsonOutput

  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [inputPath] =>
    runAnalysis inputPath none
  | [inputPath, outputPath] =>
    runAnalysis inputPath (some outputPath)
  | _ =>
    printUsage
    return 1
