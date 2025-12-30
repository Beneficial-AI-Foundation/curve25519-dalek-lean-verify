/-
  StatusCsv: Utilities for reading and writing status.csv.

  The status.csv file tracks verification status for functions with columns:
  - function: Rust function path (e.g., curve25519_dalek::backend::serial::...)
  - lean_name: Lean function name (e.g., curve25519_dalek.backend.serial....)
  - source: Source file path
  - lines: Line range in source
  - spec_theorem: Path to spec theorem file
  - extracted: Extraction status
  - verified: Verification status
  - notes: Additional notes
  - ai-proveable: AI proveability notes
-/
import Lean

open Lean

namespace Utils.StatusCsv

/-- A row in status.csv -/
structure StatusRow where
  function : String
  lean_name : String
  source : String
  lines : String
  spec_theorem : String
  extracted : String
  verified : String
  notes : String
  ai_proveable : String
  deriving Repr, Inhabited

/-- The full status.csv file -/
structure StatusFile where
  header : String
  rows : Array StatusRow
  deriving Repr

/-- Default path to status.csv -/
def defaultPath : System.FilePath := "status.csv"

/-- Split a CSV line into fields, handling basic cases -/
def splitCsvLine (line : String) : Array String :=
  -- Simple CSV parsing (assumes no quoted fields with commas)
  (line.splitOn ",").toArray

/-- Join fields into a CSV line -/
def joinCsvLine (fields : Array String) : String :=
  ",".intercalate fields.toList

/-- Parse a CSV line into a StatusRow -/
def parseRow (line : String) : Option StatusRow :=
  let fields := splitCsvLine line
  if fields.size >= 9 then
    some {
      function := fields[0]!
      lean_name := fields[1]!
      source := fields[2]!
      lines := fields[3]!
      spec_theorem := fields[4]!
      extracted := fields[5]!
      verified := fields[6]!
      notes := fields[7]!
      ai_proveable := fields[8]!
    }
  else if fields.size >= 2 then
    -- Minimal row with just function and lean_name
    some {
      function := fields[0]!
      lean_name := fields[1]!
      source := fields.getD 2 ""
      lines := fields.getD 3 ""
      spec_theorem := fields.getD 4 ""
      extracted := fields.getD 5 ""
      verified := fields.getD 6 ""
      notes := fields.getD 7 ""
      ai_proveable := ""
    }
  else
    none

/-- Convert a StatusRow to a CSV line -/
def StatusRow.toCsvLine (row : StatusRow) : String :=
  joinCsvLine #[row.function, row.lean_name, row.source, row.lines,
                row.spec_theorem, row.extracted, row.verified, row.notes, row.ai_proveable]

/-- Read and parse status.csv -/
def readStatusFile (path : System.FilePath := defaultPath) : IO StatusFile := do
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (·.trim != "")
  match lines with
  | [] => return { header := "", rows := #[] }
  | header :: dataLines =>
    let rows := dataLines.filterMap parseRow
    return { header := header, rows := rows.toArray }

/-- Write status.csv (sorted alphabetically by lean_name) -/
def writeStatusFile (file : StatusFile) (path : System.FilePath := defaultPath) : IO Unit := do
  let headerLine := file.header
  let sortedRows := file.rows.qsort (·.lean_name < ·.lean_name)
  let dataLines := sortedRows.map StatusRow.toCsvLine
  let allLines := #[headerLine] ++ dataLines
  let content := "\n".intercalate allLines.toList
  IO.FS.writeFile path (content ++ "\n")

/-- Get all lean_names from a StatusFile -/
def StatusFile.getLeanNames (file : StatusFile) : Array String :=
  file.rows.map (·.lean_name)

/-- Create a new StatusRow with just the lean_name (other fields empty) -/
def StatusRow.fromLeanName (leanName : String) : StatusRow :=
  { function := ""
    lean_name := leanName
    source := ""
    lines := ""
    spec_theorem := ""
    extracted := ""
    verified := ""
    notes := ""
    ai_proveable := "" }

/-- Add a new row to the StatusFile -/
def StatusFile.addRow (file : StatusFile) (row : StatusRow) : StatusFile :=
  { file with rows := file.rows.push row }

/-- Check if a lean_name exists in the StatusFile -/
def StatusFile.hasLeanName (file : StatusFile) (leanName : String) : Bool :=
  file.rows.any (·.lean_name == leanName)

end Utils.StatusCsv
