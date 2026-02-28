/-
  ListFuns: Pipeline for extracting and analyzing functions from Funs.lean.

  This module provides the main pipeline for:
  1. Enumerating all function definitions in a module
  2. Parsing docstrings to extract Rust metadata (source file, line numbers)
  3. Computing dependencies between functions
  4. Filtering to relevant functions (from crate source, not stdlib)
  5. Checking verification status
-/
import Lean
import Std.Data.HashSet
import Utils.Config
import Utils.Lib.Types
import Utils.Lib.Docstring
import Utils.Lib.Analysis

open Lean

namespace Utils.Lib.ListFuns

open Utils.Lib.Types
open Utils.Lib.Docstring
open Utils.Lib.Analysis
open Utils.Config

/-!
## Helper Functions
-/

/-- Check if string `s` contains substring `sub` -/
def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-!
## Filtering Functions
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

/-- Check if a name is an extraction artifact (ends with _body, _loop, etc.) -/
def isExtractionArtifactName (name : Name) : Bool :=
  let str := name.toString
  extractionArtifactSuffixes.any fun sfx => str.endsWith sfx

/-- Check if a name is in the hidden functions list -/
def isHiddenFunction (name : Name) : Bool :=
  let str := name.toString
  hiddenFunctions.any fun hidden => str == hidden

/-- Check if a name passes basic filters (prefix only, not suffix) -/
def passesBasicFilters (name : Name) : Bool :=
  !hasExcludedPrefix name


/-!
## Relevance Checking

A function is "relevant" if its source is from the target crate,
not from external sources like /rustc/ (stdlib) or /cargo/registry/ (deps).
-/

/-- Check if a source path indicates a relevant (crate-internal) function -/
def isRelevantSource (source : Option String) (crate : String) : Bool :=
  match source with
  | none => false  -- No source info -> not relevant
  | some s =>
    -- Must contain crate name and not be from external sources
    containsSubstr s crate &&
    !s.startsWith "/" &&  -- External paths start with /rustc/ or /cargo/
    !containsSubstr s "/cargo/registry/"

/-!
## Pipeline Implementation
-/

/-- Get all definition names from a module -/
def getModuleDefinitions (env : Environment) (moduleName : Name) : Array Name := Id.run do
  let some moduleIdx := env.header.moduleNames.idxOf? moduleName
    | return #[]
  let constNames := env.header.moduleData[moduleIdx]!.constNames
  let mut result : Array Name := #[]
  for name in constNames do
    if let some ci := env.find? name then
      if isDefinition ci then
        result := result.push name
  return result

/-- Get the corresponding _body name for a function -/
def getBodyName (name : Name) : Name :=
  name.appendAfter "_body"

/-- Intermediate record with raw data before filtering -/
structure RawFunctionData where
  name : Name
  docInfo : DocstringInfo
  rawDeps : Array Name
  isExtractionArtifact : Bool
  isHidden : Bool
  deriving Repr

/-- Gather raw data for a function, inheriting docstring from _body if needed -/
def gatherRawData (env : Environment) (name : Name) : IO RawFunctionData := do
  let isArtifact := isExtractionArtifactName name
  let hidden := isHiddenFunction name
  let mut docInfo ← getDocstringInfo env name

  -- If no docstring and this isn't a _body itself, try to inherit from _body
  if docInfo.rustName.isNone && !name.toString.endsWith "_body" then
    let bodyName := getBodyName name
    if env.find? bodyName |>.isSome then
      let bodyDocInfo ← getDocstringInfo env bodyName
      -- Inherit docstring info from _body
      docInfo := bodyDocInfo

  let rawDeps := match getDirectDeps env name with
    | .ok deps => deps
    | .error _ => #[]
  return { name, docInfo, rawDeps, isExtractionArtifact := isArtifact, isHidden := hidden }

/-- Read Rust source code lines from a file given path and line range -/
def getRustSourceCode (source : String) (lineStart lineEnd : Nat) : IO (Option String) := do
  let filePath : System.FilePath := source
  if !(← filePath.pathExists) then return none
  let contents ← IO.FS.readFile filePath
  let lines := contents.splitOn "\n"
  if lineStart == 0 || lineEnd == 0 || lineStart > lines.length then return none
  let relevantLines := lines.toArray.extract (lineStart - 1) lineEnd
  if relevantLines.isEmpty then return none
  return some (String.intercalate "\n" relevantLines.toList)

/-- Build a complete FunctionRecord from raw data -/
def buildFunctionRecord
    (env : Environment)
    (rawData : RawFunctionData)
    (relevantNames : Std.HashSet Name)
    (crate : String)
    : IO FunctionRecord := do
  let docInfo := rawData.docInfo
  let lineRange := match docInfo.lineStart, docInfo.lineEnd with
    | some s, some e => some (s, e)
    | _, _ => none
  let filteredDeps := rawData.rawDeps.filter (relevantNames.contains ·)
  let isRelevant := isRelevantSource docInfo.source crate
  let specParts ← getSpecParts env rawData.name
  let rustSource ← match docInfo.source, docInfo.lineStart, docInfo.lineEnd with
    | some src, some s, some e => getRustSourceCode src s e
    | _, _, _ => pure none
  return {
    leanName := rawData.name
    rustName := docInfo.rustName
    source := docInfo.source
    lineRange := lineRange
    dependencies := filteredDeps
    isRelevant := isRelevant
    isExtractionArtifact := rawData.isExtractionArtifact
    isHidden := rawData.isHidden
    isSpecified := hasSpecTheorem env rawData.name
    isVerified := isVerified env rawData.name
    isFullyVerified := isFullyVerified env relevantNames rawData.name
    isExternallyVerified := isExternallyVerified env rawData.name
    specFilePath := getSpecFilePath env rawData.name
    specDocstring := specParts.docstring
    specStatement := specParts.statement
    rustSourceCode := rustSource
  }

/-- Main pipeline: build all FunctionRecords from a module -/
def buildFunctionRecords
    (env : Environment)
    (moduleName : Name := funsModule)
    (crate : String := crateName)
    : IO (Array FunctionRecord) := do
  -- Step 1: Get all definitions from the module
  let allDefs := getModuleDefinitions env moduleName

  -- Step 2: Apply basic filters (prefix only, extraction artifacts are kept)
  let basicFiltered := allDefs.filter passesBasicFilters

  -- Step 3: Gather raw data for all functions (including nested children)
  let rawDataArray ← basicFiltered.mapM (gatherRawData env)

  -- Step 4: Build set of relevant function names
  -- (functions whose source is from the crate)
  let mut relevantNames : Std.HashSet Name := {}
  for rawData in rawDataArray do
    if isRelevantSource rawData.docInfo.source crate then
      relevantNames := relevantNames.insert rawData.name

  -- Step 5: Build FunctionRecords (deps filtered to relevant set)
  let records ← rawDataArray.mapM fun rawData =>
    buildFunctionRecord env rawData relevantNames crate

  -- Step 6: Sort alphabetically
  return records.qsort (·.leanName.toString < ·.leanName.toString)

/-- Get only the relevant functions -/
def getRelevantFunctions
    (env : Environment)
    (moduleName : Name := funsModule)
    (crate : String := crateName)
    : IO (Array FunctionRecord) := do
  let all ← buildFunctionRecords env moduleName crate
  return all.filter (·.isRelevant)

/-!
## Environment Loading
-/

/-- Load the project environment (configured via Utils.Config) -/
def loadEnvironment : IO Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  importModules #[{ module := mainModule }] {}

/-- Get all function names as strings (used by SyncStatus) -/
def getFunsDefinitionsAsStrings (env : Environment) : IO (Array String) := do
  let records ← getRelevantFunctions env
  return records.map (·.leanName.toString)

end Utils.Lib.ListFuns
