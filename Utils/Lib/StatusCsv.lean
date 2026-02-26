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
import Utils.Lib.Types

open Lean
open Utils.Lib.Types

namespace Utils.Lib.StatusCsv

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

/-- Check if string contains a substring -/
private def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Escape a field for CSV output: quote if contains comma, quote, or newline -/
def escapeField (s : String) : String :=
  if containsSubstr s "," || containsSubstr s "\"" || containsSubstr s "\n" then
    -- Escape quotes by doubling them, then wrap in quotes
    "\"" ++ s.replace "\"" "\"\"" ++ "\""
  else
    s

/-- Parse a single CSV field, handling quoted fields -/
private def parseField (s : String) : String :=
  let trimmed := s.trimAscii.toString
  if trimmed.startsWith "\"" && trimmed.endsWith "\"" && trimmed.length >= 2 then
    -- Remove surrounding quotes and unescape doubled quotes
    let inner := trimmed.drop 1 |>.dropEnd 1
    inner.replace "\"\"" "\""
  else
    s

/-- Split a CSV line into fields, handling quoted fields with commas -/
def splitCsvLine (line : String) : Array String := Id.run do
  let mut fields : Array String := #[]
  let mut current := ""
  let mut inQuotes := false
  let mut i := 0
  let chars := line.toList

  while i < chars.length do
    let c := chars[i]!
    if c == '"' then
      if inQuotes && i + 1 < chars.length && chars[i + 1]! == '"' then
        -- Escaped quote
        current := current.push '"'
        i := i + 1
      else
        -- Toggle quote state
        inQuotes := !inQuotes
    else if c == ',' && !inQuotes then
      -- End of field
      fields := fields.push current
      current := ""
    else
      current := current.push c
    i := i + 1

  -- Don't forget the last field
  fields := fields.push current
  return fields

/-- Join fields into a CSV line with proper escaping -/
def joinCsvLine (fields : Array String) : String :=
  ",".intercalate (fields.map escapeField).toList

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
  let lines := content.splitOn "\n" |>.filter (·.trimAscii.toString != "")
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

/-- Create a new StatusRow from a FunctionOutput -/
def StatusRow.fromFunctionOutput (fn : FunctionOutput) : StatusRow :=
  let verifiedStr := if fn.verified then "verified"
                     else if fn.specified then "specified"
                     else ""
  let extractedStr := if fn.is_relevant then "extracted" else ""
  { function := fn.rust_name.getD ""
    lean_name := fn.lean_name
    source := fn.source.getD ""
    lines := fn.lines.getD ""
    spec_theorem := fn.spec_file.getD ""
    extracted := extractedStr
    verified := verifiedStr
    notes := ""
    ai_proveable := "" }

/-- Check if two StatusRows have the same updatable fields -/
def StatusRow.sameUpdatableFields (a b : StatusRow) : Bool :=
  a.function == b.function &&
  a.source == b.source &&
  a.lines == b.lines &&
  a.spec_theorem == b.spec_theorem &&
  a.extracted == b.extracted &&
  a.verified == b.verified

/-- Update an existing StatusRow with data from FunctionOutput.
    Preserves: notes, ai_proveable -/
def StatusRow.updateFrom (row : StatusRow) (fn : FunctionOutput) : StatusRow :=
  let verifiedStr := if fn.verified then "verified"
                     else if fn.specified then "specified"
                     else ""
  let extractedStr := if fn.is_relevant then "extracted" else ""
  { row with
    function := fn.rust_name.getD row.function
    source := fn.source.getD row.source
    lines := fn.lines.getD row.lines
    spec_theorem := fn.spec_file.getD row.spec_theorem
    extracted := extractedStr
    verified := verifiedStr }

/-- Add a new row to the StatusFile -/
def StatusFile.addRow (file : StatusFile) (row : StatusRow) : StatusFile :=
  { file with rows := file.rows.push row }

/-- Check if a lean_name exists in the StatusFile -/
def StatusFile.hasLeanName (file : StatusFile) (leanName : String) : Bool :=
  file.rows.any (·.lean_name == leanName)

/-- Find a row by lean_name -/
def StatusFile.findByLeanName (file : StatusFile) (leanName : String) : Option StatusRow :=
  file.rows.find? (·.lean_name == leanName)

/-- Update or add a row based on FunctionOutput -/
def StatusFile.upsertFromFunction (file : StatusFile) (fn : FunctionOutput) : StatusFile :=
  let idx := file.rows.findIdx? (·.lean_name == fn.lean_name)
  match idx with
  | some i =>
    -- Update existing row
    let updatedRow := file.rows[i]!.updateFrom fn
    { file with rows := file.rows.set! i updatedRow }
  | none =>
    -- Add new row
    file.addRow (StatusRow.fromFunctionOutput fn)

/-- Remove rows whose lean_name is in the given set -/
def StatusFile.removeByLeanNames (file : StatusFile) (names : Std.HashSet String) : StatusFile :=
  { file with rows := file.rows.filter fun row => !names.contains row.lean_name }

/-- Find duplicate lean_names in the StatusFile. Returns array of lean_names that appear more than once. -/
def StatusFile.findDuplicateLeanNames (file : StatusFile) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut duplicates : Std.HashSet String := {}
  for row in file.rows do
    if seen.contains row.lean_name then
      duplicates := duplicates.insert row.lean_name
    else
      seen := seen.insert row.lean_name
  return duplicates.toArray.qsort (· < ·)

/-- Remove duplicate rows by lean_name, keeping only the first occurrence. -/
def StatusFile.deduplicate (file : StatusFile) : StatusFile := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut uniqueRows : Array StatusRow := #[]
  for row in file.rows do
    if !seen.contains row.lean_name then
      seen := seen.insert row.lean_name
      uniqueRows := uniqueRows.push row
  return { file with rows := uniqueRows }

end Utils.Lib.StatusCsv
