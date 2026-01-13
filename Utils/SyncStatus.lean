/-
  SyncStatus: Synchronize status.csv with functions from Funs.lean.

  This tool:
  1. Regenerates functions.json by running the listfuns pipeline
  2. Reads the existing status.csv
  3. For each function in functions.json:
     - If not in status.csv, adds a new row
     - If already in status.csv, updates: rust_name, source, lines, extracted, verified
     - Preserves: spec_theorem, notes, ai_proveable
  4. Writes the updated status.csv
-/
import Cli
import Std.Data.HashSet
import Utils.Config
import Utils.Lib.ListFuns
import Utils.Lib.StatusCsv
import Utils.Lib.Types

open Cli
open Utils.Config
open Utils.Lib.StatusCsv
open Utils.Lib.ListFuns
open Utils.Lib.Types

/-- Run the syncstatus command -/
def runSyncStatus (p : Parsed) : IO UInt32 := do
  let csvPathStr : String := match p.variableArgsAs? String with
    | some args => args[0]?.getD "status.csv"
    | none => "status.csv"
  let csvPath : System.FilePath := csvPathStr

  -- Step 1: Load Lean environment and regenerate function data
  IO.eprintln s!"Loading {mainModule} module..."
  let env ← loadEnvironment
  IO.eprintln "Module loaded successfully"

  IO.eprintln "Generating function records..."
  let records ← getRelevantFunctions env
  let allOutputs := records.map FunctionRecord.toOutput
  IO.eprintln s!"Found {allOutputs.size} relevant functions"

  -- Step 2: Write functions.json (includes ALL functions)
  let jsonPath : System.FilePath := "functions.json"
  let output : FunctionListOutput := { functions := allOutputs }
  IO.FS.writeFile jsonPath (renderFunctionListOutput output)
  IO.eprintln s!"Updated {jsonPath}"

  -- Step 3: Filter for status.csv (exclude hidden and extraction artifacts)
  let csvOutputs := allOutputs.filter fun fn => !fn.is_hidden && !fn.is_extraction_artifact
  IO.eprintln s!"  {csvOutputs.size} functions for status.csv (excluding hidden and artifacts)"

  -- Step 4: Read current status.csv
  IO.eprintln s!"Reading {csvPath}..."
  let statusFile ← readStatusFile csvPath
  IO.eprintln s!"Found {statusFile.rows.size} existing entries in status.csv"

  -- Step 5: Sync filtered functions (update existing, add new)
  let mut updatedFile := statusFile
  let mut addedCount := 0
  let mut updatedCount := 0

  for fn in csvOutputs do
    match updatedFile.findByLeanName fn.lean_name with
    | some existingRow =>
      let newRow := existingRow.updateFrom fn
      if !existingRow.sameUpdatableFields newRow then
        updatedCount := updatedCount + 1
      updatedFile := updatedFile.upsertFromFunction fn
    | none =>
      addedCount := addedCount + 1
      IO.eprintln s!"  Adding: {fn.lean_name}"
      updatedFile := updatedFile.upsertFromFunction fn

  -- Step 5: Write updated file
  writeStatusFile updatedFile csvPath

  IO.println s!"Sync complete:"
  IO.println s!"  - {addedCount} new functions added"
  IO.println s!"  - {updatedCount} existing functions updated"
  IO.println s!"  - Total entries: {updatedFile.rows.size}"

  return 0

/-- The syncstatus command definition -/
def syncstatusCmd : Cmd := `[Cli|
  syncstatus VIA runSyncStatus; ["0.1.0"]
  "Synchronize status.csv with functions from Funs.lean.

Updates functions.json and syncs status.csv:
- Adds new functions not yet in status.csv
- Updates existing rows with current: rust_name, source, lines, verified status
- Preserves manual fields: spec_theorem, notes, ai_proveable"

  ARGS:
    ...path : String; "Path to status.csv (default: status.csv)"
]

/-- Main entry point -/
def main (args : List String) : IO UInt32 :=
  syncstatusCmd.validate args
