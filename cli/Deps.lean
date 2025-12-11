/-
  Deps: A CLI tool to find dependencies of Lean functions.

  Usage:
    lake exe deps <input.json> [output.json]

  Input JSON format:
    { "functions": [{ "lean_name": "curve25519_dalek.some.function" }, ...] }

  Output JSON format:
    {
      "functions": [
        { "lean_name": "...", "dependencies": ["...", ...] }
      ]
    }

  Exits with code 1 on any error.

  Example:
    lake exe deps functions.json deps.json
-/
import Lean
import Std.Data.HashSet
import cli.Json
import cli.Analysis

open Lean
open cli.Json
open cli.Analysis

/-- Print usage information -/
def printUsage : IO Unit := do
  IO.println "Usage: lake exe deps <input.json> [output.json]"
  IO.println ""
  IO.println "Analyzes Lean function dependencies."
  IO.println ""
  IO.println "Arguments:"
  IO.println "  <input.json>   JSON file with functions to analyze"
  IO.println "  [output.json]  Output file (prints to stdout if omitted)"
  IO.println ""
  IO.println "Input format:"
  IO.println "  { \"functions\": [{ \"name\": \"some.function.name\" }, ...] }"
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

  -- Import the main module
  IO.println "Loading Curve25519Dalek.Funs module..."
  let env ← importModules #[{ module := `Curve25519Dalek.Funs }] {}
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
      }
      results := results.push output

  IO.println s!"Analysis complete: {results.size} functions analyzed"

  -- Build output
  let output : AnalysisOutput := {
    results := results
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
