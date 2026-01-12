/-
  SyncStatus: Synchronize status.csv with functions from Funs.lean.
-/
import Cli
import Std.Data.HashSet
import Utils.Config
import Utils.Lib.ListFuns
import Utils.Lib.StatusCsv

open Cli
open Utils.Config
open Utils.Lib.StatusCsv
open Utils.Lib.ListFuns

/-- Run the syncstatus command -/
def runSyncStatus (p : Parsed) : IO UInt32 := do
  let csvPathStr : String := match p.variableArgsAs? String with
    | some args => args[0]?.getD "status.csv"
    | none => "status.csv"
  let csvPath : System.FilePath := csvPathStr

  -- Read current status.csv
  IO.eprintln s!"Reading {csvPath}..."
  let statusFile ← readStatusFile csvPath
  IO.eprintln s!"Found {statusFile.rows.size} existing entries"

  -- Load Lean environment and get functions
  IO.eprintln s!"Loading {mainModule} module..."
  let env ← loadEnvironment
  IO.eprintln "Module loaded successfully"

  let funNames ← getFunsDefinitionsAsStrings env
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

/-- The syncstatus command definition -/
def syncstatusCmd : Cmd := `[Cli|
  syncstatus VIA runSyncStatus; ["0.1.0"]
  "Synchronize status.csv with functions from Funs.lean."

  ARGS:
    ...path : String; "Path to status.csv (default: status.csv)"
]

/-- Main entry point -/
def main (args : List String) : IO UInt32 :=
  syncstatusCmd.validate args
