/-
  ListFuns: CLI entry point for listfuns executable.
-/
import Cli
import Utils.Config
import Utils.Lib.ListFuns
import Utils.Lib.Types

open Cli
open Utils.Config
open Utils.Lib.ListFuns
open Utils.Lib.Types

/-- Run the listfuns command -/
def runListFuns (p : Parsed) : IO UInt32 := do
  let includeAll := p.hasFlag "all"
  let outputPath : Option String := match p.variableArgsAs? String with
    | some args => args[0]?
    | none => none

  -- Load environment
  IO.eprintln s!"Loading {mainModule} module..."
  let env ← loadEnvironment
  IO.eprintln "Module loaded successfully"

  -- Build function records
  let allRecords ← buildFunctionRecords env
  let records := if includeAll then allRecords else allRecords.filter (·.isRelevant)
  IO.eprintln s!"Found {records.size} functions (of {allRecords.size} total)"

  -- Build output
  let functions := records.map FunctionRecord.toOutput
  let output : FunctionListOutput := { functions }

  -- Write or print output
  let jsonOutput := renderFunctionListOutput output
  match outputPath with
  | some path =>
    IO.FS.writeFile path jsonOutput
    IO.println s!"Results written to {path}"
  | none =>
    IO.println jsonOutput

  return 0

/-- The listfuns command definition -/
def listfunsCmd : Cmd := `[Cli|
  listfuns VIA runListFuns; ["0.1.0"]
  "List functions from Funs.lean with dependencies and verification status."

  FLAGS:
    a, all; "Include all functions, not just relevant ones"

  ARGS:
    ...output : String; "Output JSON file (prints to stdout if omitted)"
]

/-- Main entry point -/
def main (args : List String) : IO UInt32 :=
  listfunsCmd.validate args
