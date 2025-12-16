/-
  Analysis: Core dependency analysis logic.
-/
import Lean
import Std.Data.HashSet

open Lean

namespace Utils.Analysis

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

/-- Compute transitive dependencies within a set of known functions -/
partial def getTransitiveDeps (env : Environment) (knownNames : Std.HashSet Name) (name : Name)
    (visited : Std.HashSet Name := {}) : Std.HashSet Name :=
  if visited.contains name then visited
  else
    let visited := visited.insert name
    match getDirectDeps env name with
    | .error _ => visited
    | .ok deps =>
      let filteredDeps := filterToKnownFunctions knownNames deps
      filteredDeps.foldl (fun acc dep => getTransitiveDeps env knownNames dep acc) visited

/-- Check if a function and all its transitive dependencies are verified -/
def isFullyVerified (env : Environment) (knownNames : Std.HashSet Name) (name : Name) : Bool :=
  -- First check if the function itself is verified
  if !isVerified env name then false
  else
    -- Get all transitive dependencies (excluding the function itself)
    let allDeps := getTransitiveDeps env knownNames name
    let transitiveDeps := allDeps.erase name
    -- Check if all transitive dependencies are verified
    transitiveDeps.all (isVerified env)

end Utils.Analysis
