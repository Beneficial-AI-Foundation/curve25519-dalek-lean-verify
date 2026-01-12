/-
  Analysis: Core dependency analysis logic.

  This module provides functions for analyzing Lean constants to determine:
  - Their dependencies on other constants
  - Whether they have a specification theorem (`{name}_spec`)
  - Whether that specification is fully proven (no `sorry`)
  - Whether all transitive dependencies are also verified

  TODO: The suffix-based exclusion of `_loop`, `_body` etc. in ListFuns.lean is a workaround.
  The proper fix is to make the verification checker understand that verifying a function
  like `foo` should consider `foo_loop` as part of `foo`'s implementation, not as a separate
  function requiring its own spec. This requires understanding Aeneas extraction patterns better.
-/
import Lean
import Lean.PrettyPrinter
import Std.Data.HashSet

open Lean
open Lean.Meta
open Lean.PrettyPrinter

namespace Utils.Lib.Analysis

/-!
## Environment Reader Monad

A simple reader monad for functions that need MonadEnv.
-/

/-- Simple reader monad over Environment for pure MonadEnv operations -/
abbrev EnvM := ReaderT Environment Id

instance : MonadEnv EnvM where
  getEnv := read
  modifyEnv _ := pure ()

/-- Suffix appended to function names to form spec theorem names.
    Convention: for function `foo`, the spec theorem is `foo_spec`. -/
def specSuffix : String := "_spec"

/-- Get direct dependencies of a constant from its value expression -/
def getDirectDeps (env : Environment) (name : Name) : Except String (Array Name) := do
  let some constInfo := env.find? name
    | throw s!"Constant '{name}' not found in environment"
  let some value := constInfo.value?
    | throw s!"Constant '{name}' has no value (it may be an axiom, opaque, or primitive)"
  return value.getUsedConstants

/-- Filter dependencies to only include names in the given set -/
def filterToKnownFunctions (knownNames : Std.HashSet Name) (deps : Array Name) : Array Name :=
  deps.filter (fun name => knownNames.contains name)

/-- Check if a spec theorem exists for the given function name -/
def hasSpecTheorem (env : Environment) (name : Name) : Bool :=
  let specName := name.appendAfter specSuffix
  env.find? specName |>.isSome

/-- Check if a proof directly contains sorry (sorryAx) -/
def proofContainsSorry (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some constInfo =>
    match constInfo.value? with
    | some value => value.getUsedConstants.any (· == ``sorryAx)
    | none => true  -- No value means axiom/opaque, treat as not verified
  | none => true

/-- Check if a function is verified (has spec theorem without direct sorry) -/
def isVerified (env : Environment) (name : Name) : Bool :=
  let specName := name.appendAfter specSuffix
  match env.find? specName with
  | some _ => !proofContainsSorry env specName
  | none => false

/-- Get the spec theorem statement as a pretty-printed string.
    Returns the theorem type (the proposition being proved). -/
def getSpecStatement (env : Environment) (name : Name) : IO (Option String) := do
  let specName := name.appendAfter specSuffix
  match env.find? specName with
  | none => return none
  | some constInfo =>
    let type := constInfo.type
    -- Run MetaM to pretty-print the expression
    let (fmt, _) ← (Meta.ppExpr type).run'.toIO
      { fileName := "", fileMap := default }
      { env := env }
    return some (Format.pretty fmt)

/-- Result of extracting spec theorem parts from source -/
structure SpecParts where
  docstring : Option String := none
  statement : Option String := none
  deriving Repr, Inhabited

/-- Get the spec theorem docstring and statement from the source file.
    Returns (docstring, statement) where statement excludes the proof. -/
def getSpecParts (env : Environment) (name : Name) : IO SpecParts := do
  let specName := name.appendAfter specSuffix
  -- Check if the theorem exists
  if env.find? specName |>.isNone then return {}
  -- Get declaration ranges using the EnvM reader monad
  let rangesOpt : Option DeclarationRanges := (findDeclarationRangesCore? specName : EnvM _).run env
  match rangesOpt with
  | none => return {}
  | some ranges =>
    -- Get the module that contains this declaration
    let some modIdx := env.getModuleIdxFor? specName | return {}
    let moduleName := env.allImportedModuleNames[modIdx.toNat]!
    -- Convert module name to file path (e.g., Curve25519Dalek.Specs.Foo -> Curve25519Dalek/Specs/Foo.lean)
    let filePath : System.FilePath := moduleName.toString.replace "." "/" ++ ".lean"
    -- Check if file exists
    if !(← filePath.pathExists) then return {}
    -- Read the source file
    let contents ← IO.FS.readFile filePath
    let lines := contents.splitOn "\n"
    -- Extract lines from start to end (1-indexed in Lean positions)
    let range := ranges.range
    let startLine := range.pos.line
    let endLine := range.endPos.line
    if startLine == 0 || endLine == 0 then return {}
    let relevantLines := lines.toArray.extract (startLine - 1) endLine
    -- Separate docstring from statement
    let mut docstringLines : Array String := #[]
    let mut statementLines : Array String := #[]
    let mut inDocstring := false
    let mut docstringDone := false
    for line in relevantLines do
      if !docstringDone then
        -- Check for docstring start
        if line.trimLeft.startsWith "/-" then
          inDocstring := true
          docstringLines := docstringLines.push line
        else if inDocstring then
          docstringLines := docstringLines.push line
          if (line.splitOn "-/").length > 1 then
            inDocstring := false
            docstringDone := true
        else if line.trimLeft.startsWith "@[" then
          -- Skip attribute declarations (e.g., @[progress], @[simp])
          -- Mark docstring as done so we continue looking for theorem
          docstringDone := true
          continue
        else if line.trimLeft.startsWith "theorem" then
          -- Start of statement
          docstringDone := true
          -- Check if this line contains `:= by`
          let parts := line.splitOn ":= by"
          if parts.length > 1 then
            statementLines := statementLines.push (parts[0]!.trimRight ++ " := by ...")
          else if line.trimRight.endsWith ":=" then
            statementLines := statementLines.push (line.trimRight ++ " ...")
          else
            statementLines := statementLines.push line
        else
          -- Skip empty lines or other content before docstring/statement
          continue
      else
        -- Processing statement (skip any remaining attribute lines)
        if line.trimLeft.startsWith "@[" then
          continue
        let parts := line.splitOn ":= by"
        if parts.length > 1 then
          statementLines := statementLines.push (parts[0]!.trimRight ++ " := by ...")
          break
        else if line.trimRight.endsWith ":=" then
          statementLines := statementLines.push (line.trimRight ++ " ...")
          break
        else
          statementLines := statementLines.push line
    let docstring := if docstringLines.isEmpty then none
      else some (String.intercalate "\n" docstringLines.toList)
    let statement := if statementLines.isEmpty then none
      else some (String.intercalate "\n" statementLines.toList)
    return { docstring, statement }

/-- Result of analyzing a single function -/
structure AnalysisResult where
  name : Name
  allDeps : Array Name
  filteredDeps : Array Name
  /-- True if a spec theorem exists for this function (i.e., `{name}_spec` is defined) -/
  specified : Bool
  /-- True if specified AND the spec theorem's proof contains no `sorry` -/
  verified : Bool
  error : Option String := none
  deriving Repr

/-- Analyze a single function in the given environment -/
def analyzeFunction (env : Environment) (knownNames : Std.HashSet Name) (name : Name) : AnalysisResult :=
  match getDirectDeps env name with
  | .ok deps =>
    { name := name
      allDeps := deps
      filteredDeps := filterToKnownFunctions knownNames deps
      specified := hasSpecTheorem env name
      verified := isVerified env name
      error := none }
  | .error msg =>
    { name := name
      allDeps := #[]
      filteredDeps := #[]
      specified := false
      verified := false
      error := some msg }

/-- Analyze multiple functions -/
def analyzeFunctions (env : Environment) (knownNames : Std.HashSet Name) (names : List Name) : List AnalysisResult :=
  names.map (analyzeFunction env knownNames)

/-- Try to find a constant by exact name -/
def resolveConstantName (env : Environment) (nameStr : String) : Option Name :=
  let name := nameStr.toName
  if env.find? name |>.isSome then some name else none

/-- Compute transitive dependencies within a set of known functions.
    Returns the set of all reachable dependencies and a list of any errors encountered. -/
partial def getTransitiveDepsWithErrors (env : Environment) (knownNames : Std.HashSet Name) (name : Name)
    (visited : Std.HashSet Name := {}) (errors : Array String := #[]) : Std.HashSet Name × Array String :=
  if visited.contains name then (visited, errors)
  else
    let visited := visited.insert name
    match getDirectDeps env name with
    | .error msg =>
      -- Record error but continue traversal
      (visited, errors.push s!"Warning: {msg}")
    | .ok deps =>
      let filteredDeps := filterToKnownFunctions knownNames deps
      filteredDeps.foldl
        (fun (acc, errs) dep => getTransitiveDepsWithErrors env knownNames dep acc errs)
        (visited, errors)

/-- Compute transitive dependencies within a set of known functions.
    Logs warnings to stderr for any errors encountered during traversal. -/
partial def getTransitiveDeps (env : Environment) (knownNames : Std.HashSet Name) (name : Name)
    (visited : Std.HashSet Name := {}) : IO (Std.HashSet Name) := do
  let (result, errors) := getTransitiveDepsWithErrors env knownNames name visited
  for err in errors do
    IO.eprintln err
  return result

/-- Pure version that silently ignores errors (for backwards compatibility) -/
partial def getTransitiveDeps' (env : Environment) (knownNames : Std.HashSet Name) (name : Name)
    (visited : Std.HashSet Name := {}) : Std.HashSet Name :=
  if visited.contains name then visited
  else
    let visited := visited.insert name
    match getDirectDeps env name with
    | .error _ => visited
    | .ok deps =>
      let filteredDeps := filterToKnownFunctions knownNames deps
      filteredDeps.foldl (fun acc dep => getTransitiveDeps' env knownNames dep acc) visited

/-- Check if a function and all its transitive dependencies are verified -/
def isFullyVerified (env : Environment) (knownNames : Std.HashSet Name) (name : Name) : Bool :=
  -- First check if the function itself is verified
  if !isVerified env name then false
  else
    -- Get all transitive dependencies (excluding the function itself)
    let allDeps := getTransitiveDeps' env knownNames name
    let transitiveDeps := allDeps.erase name
    -- Check if all transitive dependencies are verified
    transitiveDeps.all (isVerified env)

end Utils.Lib.Analysis
