/-
  SyncStatus: Synchronize status.csv with functions from Funs.lean.

  This tool:
  1. Reads the current status.csv
  2. Extracts all function definitions from Funs.lean
  3. Identifies functions not yet in status.csv
  4. Adds new rows for missing functions

  Usage:
    lake exe syncstatus [status.csv]

  If no path is specified, uses "status.csv" in the current directory.
-/
import Utils.ListFuns
import Utils.StatusCsv
import Std.Data.HashSet

open Utils.StatusCsv

/-- Print usage information -/
def printUsage : IO Unit := do
  IO.println "Usage: lake exe syncstatus [status.csv]"
  IO.println ""
  IO.println "Synchronizes status.csv with functions from Funs.lean."
  IO.println ""
  IO.println "Arguments:"
  IO.println "  [status.csv]  Path to status file (default: status.csv)"
  IO.println ""
  IO.println "This tool adds new rows for any functions in Funs.lean"
  IO.println "that are not already present in status.csv."

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  let csvPath : System.FilePath := args.head?.getD "status.csv"

  -- Read current status.csv
  IO.eprintln s!"Reading {csvPath}..."
  let statusFile ← readStatusFile csvPath
  IO.eprintln s!"Found {statusFile.rows.size} existing entries"

  -- Load Lean environment and get functions
  IO.eprintln "Loading Curve25519Dalek module..."
  let env ← Utils.ListFuns.loadEnvironment
  IO.eprintln "Module loaded successfully"

  let funNames ← Utils.ListFuns.getFunsDefinitionsAsStrings env
  IO.eprintln s!"Found {funNames.size} functions in Funs.lean"

  -- Find functions not in status.csv
  let existingNames := statusFile.getLeanNames
  let existingSet : Std.HashSet String := existingNames.foldl (·.insert ·) {}

  let newFunctions := funNames.filter (!existingSet.contains ·)

  if newFunctions.isEmpty then
    IO.println "No new functions to add. status.csv is up to date."
    return 0

  IO.eprintln s!"Found {newFunctions.size} new functions to add"

  -- Add new rows
  let mut updatedFile := statusFile
  for funName in newFunctions do
    let newRow := StatusRow.fromLeanName funName
    updatedFile := updatedFile.addRow newRow
    IO.eprintln s!"  Adding: {funName}"

  -- Write updated file
  writeStatusFile updatedFile csvPath
  IO.println s!"Updated {csvPath} with {newFunctions.size} new entries"
  IO.println s!"Total entries: {updatedFile.rows.size}"

  return 0
